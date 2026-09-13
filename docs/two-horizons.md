# Two Horizons: Coarse-Graining Defects, Fluid Computation, and Regularity Budgets

## A position paper on the SGC -> Miranda-Moore -> Navier-Stokes program, written the week forced Navier-Stokes blowup was formalized

**Jason Shroyer** (SGC project), with drafting assistance. Version 0.2, 2026-09-13. Two rounds of external adversarial review applied; see the change log at the end.
Status: internal preprint. Every mathematical claim carries one of four labels:
**[KERNEL]** kernel-checked in Lean 4 in `sgc-lean` (declaration named);
**[EXTERNAL]** published or publicly released by others, cited;
**[FRAMING]** an analogy or dictionary we find useful and have not proved;
**[CONJECTURE]** a precise open statement we propose.
A claim map (Section 9) lists every declaration named here and what it does and does
not establish. This paper was itself run through the discipline described in Section 8.

---

### Abstract

We describe a research program connecting three bodies of work: (i) SGC (Spectral
Geometry of Consolidation), a Lean 4 library of kernel-checked theorems about when a
finite-state Markov generator admits a faithful coarse-grained description, how long
that description stays valid, and how its geometry (Bakry-Emery curvature) and
computational content behave under coarse-graining; (ii) the Miranda program
(Cardona, Miranda, Peralta-Salas, and coauthors) realizing Turing-complete dynamics in
steady Euler and stationary Navier-Stokes flows, built on Moore's generalized shifts;
and (iii) the regularity problem for 3D incompressible fluids, which on 2026-09-08
acquired a public, self-assessed, kernel-checked Lean artifact establishing forced
finite-time breakdown (Clay alternatives C and D) and unforced Euler blowup with
divergent Beale-Kato-Majda budget.

Our thesis is that these involve two *horizon functionals* that must be kept distinct:
a **validity horizon** - a certified time over which a coarse description tracks the
projected fine dynamics, bounded below by an inverse power of a closure defect
(sufficient, not iff) - and a **continuation budget** `B(T) = int_0^T W` whose
finiteness is *necessary* for continuation in the Beale-Kato-Majda sense (again not an
equivalence). SGC has kernel-proven the discrete validity-horizon theorem, exact
lumpability of a Bernoulli shift tower, the undecidability of a global curvature bound
via a compiler against Mathlib's Turing machines, an abstract continuation-budget
theorem (L0), a residual-controlled tracking theorem, and - new in v0.2 - a statistical
horizon theorem for Koopman-type operators with a conditional-expectation projection.
Two rounds of adversarial review removed from this paper every unproved equivalence
between these objects: the identification of the defect with energy flux, the
fixed-cutoff collapse conjecture, and the identification of the shift tower with
Moore's Turing simulation. What remains is a set of kernel-checked theorems, a
specification for the first Galerkin-level result (residual-controlled, with prior art
cited), and a statistical bridge with its first regression test. We claim no result
about the unforced Navier-Stokes regularity problem.

---

## 1. The state of Navier-Stokes, 2026-09-12

### 1.1 What was released **[EXTERNAL]**

On 2026-09-08 OpenAI released two manuscripts, "Finite time blowup for Navier-Stokes"
(166 pp.) and "Finite time blowup for the Euler equation" (57 pp.), and a Lean 4
repository `openai/NavierStokesAndEuler` (toolchain `v4.34.0-rc2`, Mathlib, 2659 Lean
files). The repository's `formalization.yaml` declares four main results with
`sorry_count: 0` and axioms `propext, Classical.choice, Quot.sound`, and
`review.status: "self-assessed"`. The Navier-Stokes targets are stated against a
Comparator challenge file adapted from DeepMind's `formal-conjectures` formalization of
Fefferman's problem statement; the kernel-level statement of alternative (C) is

```
theorem navier_stokes_breakdown_R3 (nu : R) (hnu : nu > 0) :
  exists (u0 : R^3 -> R^3) (f : R^3 -> R -> R^3),
    InitialVelocityConditionDecay u0 /\ ForceConditionDecay f /\
    not (exists v p, NavierStokesExistenceAndSmoothnessRn nu u0 f v p)
```

i.e. for every viscosity there exist smooth decaying initial data and a smooth
decaying force for which no global smooth solution with uniformly bounded kinetic
energy exists. The paper's Theorem 1.1 is sharper: `u(.,0) = 0`, `f` compactly
supported in space-time, `(u,p)` smooth on `[0,1)` with `sup ||u||_L2 < inf` and
`limsup_{t->1} ||u||_Linf = inf`. Alternative (D) follows by periodization.

The Euler result: there is `u0 in C_c^inf`, divergence-free, whose smooth Euler
solution has finite maximal lifespan `T`, with `limsup ||u||_Linf = inf` and
`int_0^T ||curl u||_Linf dt = inf`.

Independently and hours earlier, Buckmaster and Alpoge released forced blowup for
incompressible porous media, Boussinesq, and 3D Euler, also with Lean certificates
(`tristanbuckmaster/fluid_lean`, toolchain 4.32.2). Both programs descend from the
Cordoba - Martinez-Zoroa approach of successive amplification of concentrated vortex
layers.

### 1.2 What is and is not established

| Statement | Status |
|---|---|
| Public Lean artifact exists, three standard axioms, zero `sorry` | yes (self-reported; line-count audits by third parties agree) |
| Artifact formalizes Clay alternatives C and D (forced breakdown) | yes, against the formal-conjectures statement file |
| Independent replay by this project | **no** (we read source; we did not build untrusted code - see Section 8) |
| Independent expert mathematical acceptance | not established |
| Clay alternatives A/B (unforced regularity) settled | **no**; the release says so explicitly |

The correct public sentence is: *a self-assessed, kernel-checked Lean proof that smooth
forcing can drive 3D Navier-Stokes to finite-time breakdown at every viscosity with
bounded energy, and that unforced 3D Euler can blow up from smooth compact data.* Not
"Navier-Stokes is solved".

### 1.3 The mechanism, in one paragraph **[EXTERNAL]**

The Navier-Stokes construction is an axisymmetric self-similar vortex whose core
contracts radially like `tau^{1/2}` and axially like `tau^{1/2-h}` (`tau = 1 - t`),
with inward spiral, axial outflow, and spin-up by near-conservation of angular
momentum; the momentum residual is then cancelled to every order by oscillatory
corrections (in the lineage of Craik-Criminale waves and Daneri - Szekelyhidi stress
realization) so that the *force* remains smooth through the singular time. Nothing in
the construction embeds computation. This matters below: the singularity is produced
by scale collapse, not by a program.

---

## 2. SGC in one section

SGC studies a finite-state Markov generator `L` (a matrix on a finite set `V`, rows
summing to zero) together with a partition `P` of `V` into macrostates and a
stationary measure `pi`. Three objects organize everything:

- the **coarse projector** `Pi` (conditional expectation onto block-constant
  functions) and the **coarse generator** `L-bar = Pi L Pi` (the canonical macro-law);
- the **lumpability defect** `D = (I - Pi) L Pi`, whose `pi`-weighted operator norm
  `epsilon = ||D||_pi` measures leakage out of the coarse subspace; `epsilon = 0` is
  exact (strong) lumpability;
- the **validity horizon**: the time over which the macro-law reproduces the
  projected micro-dynamics to a given tolerance.

The principal kernel-checked results, with their Lean names:

**Theorem 2.1 (Kernel Horizon) [KERNEL]** `SGC.Renormalization.KernelHorizon.kernel_closure_error_le`.
For a row-stochastic kernel `T` with closure commutator `C_T`,
`||T^n K - K (T-hat^pi)^n||_{Linf->Linf} <= n ||C_T||`. Hence
(`within_tolerance_of_defect_small`) every step count with `n ||C_T|| <= eta` lies
inside the tolerance-`eta` validity horizon: the horizon scales inversely in the
defect.

**Theorem 2.2 (Defect-Horizon bound, continuous time) [KERNEL]**
`SGC.Bridge.DefectHorizonBridge.defect_horizon_bound`. For block-constant `f0`,
`||e^{tL} f0 - e^{t L-bar} f0||_pi <= t ||D||_pi e^{t(||L-D||_pi + ||D||_pi)} ||f0||_pi`,
with explicit constants; the abstract `epsilon` of the Banach-algebra perturbation
theory *equals* the concrete defect (`defect_eq_validity_leakage`). This retired the
project's earlier trusted axioms (`TrajectoryClosure.lean`).

**Theorem 2.3 (Curvature descends along exact quotients) [KERNEL]**
`SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient`. If `L` satisfies
the Bakry-Emery condition `CD(rho, inf)` and `P` is exactly lumpable, the quotient
generator satisfies `CD(rho, inf)`; the whole Gamma-calculus intertwines. The
mathematics is Pedrotti - Salez (arXiv:2501.13079, Section 2.2) **[EXTERNAL]**; the
kernel-checked formalization and the strict-improvement witness
`StarExample.curvature_hiding` (a fine chain violating `CD(0,inf)` whose quotient
satisfies `CD(9/2, inf)`) are ours.

**Theorem 2.4 (Global curvature bound is Pi^0_1-hard) [KERNEL]**
`SGC.Bridge.HaltingCompiler.cd0_compiled_iff`: for Mathlib's `Turing.TM0` machines,
`CD0 (haltW (haltMarker M w)) <-> not (TM0.eval M w).Dom`. A single edge of rate 4 on
the otherwise unit-rate line `Z` breaks `CD(0,inf)` (`not_cd0_of_heavy_edge`); the
compiler places that edge at the halting step. Pointwise curvature stays computable
(Cushing - Kamtue - Liu - Peyerimhoff **[EXTERNAL]**); the *global* bound is
equivalent to non-halting.

**Theorem 2.5 (Bernoulli shift tower is exactly lumpable) [KERNEL; re-scoped v0.2]**
`SGC.Bridge.CantorShiftTower.shiftTower_defect_zero`, `shiftTower_stronglyLumpable`,
`shiftTower_quotient_realizes`, `truncate_pathShift`. The **uniform fresh-symbol
(Bernoulli) shift kernels** `shiftKernel p n` on depth-`n` cylinder words form an exact
(`epsilon = 0`) strongly lumpable tower under deletion of the oldest symbol; the quotient
of the depth-`(n+1)` kernel is the depth-`n` kernel; the truncation maps intertwine the
one-sided shift on `p`-adic path space (using a depth-`(n+1)` input for the next
depth-`n` window). *Not established:* any relation to Moore's generalized shifts
(finite-window rewriting, variable shifts, an explicit simulation relation) or to their
embedding in fluid flows. v0.1 called this "Moore's shift is renormalization-
transparent"; the definitions do not support that description (external review).

**Theorem 2.8 (Residual Horizon) [KERNEL, v0.1.3]** see Section 6.1'''.

**Theorem 2.9 (Statistical Horizon) [KERNEL, v0.2]**
`SGC.Bridge.StatisticalHorizon.statistical_forecast_horizon`. Normed space `E`,
operator `U` with `||U|| <= 1`, projection `P` with `P * P = P`, `||P|| <= 1`, coarse
predictor `A = P U P`, closure defect `delta = ||(1 - P) U P||`. Then
`||U^m P - A^m P|| <= m delta` and `||P U^m P - A^m P|| <= m delta`; `delta = 0`
forces exact forecasting. Intended instance: `E = L^2(mu)` for an invariant measure,
`U` the Koopman operator, `P` conditional expectation onto a finite partition. The
regression test `fourCycle_K2_ne_K1_sq` records that averaged one-step statistics of a
measure-preserving system need not compose (`K_2 != K_1^2` for the four-cycle over two
cells), which is exactly what `delta > 0` quantifies. Statement and counterexample were
supplied by the external reviewer; the formalization is ours.

**Theorem 2.6 (Discrete fluid dictionary, B1-B7) [KERNEL]**
`SGC.Bridge.DiscreteFluidDynamics`: for the probability current
`J(x,y) = pi_x L_xy - pi_y L_yx`, stationarity iff divergence-free
(`stationary_iff_current_divergence_free`), zero current iff detailed balance,
non-equilibrium steady state iff a positive-current cycle exists
(`ness_has_current_cycle`), every quotient is realized by a uniform lift
(`uniformLift_*`), the energy defect equals total current mass
(`killingDefect = ||J||_F^2`), and `int_0^inf e^{-nu t} dt = 1/nu`
(`viscous_time_budget`). The table mapping these to steady Euler / contact geometry is
**[FRAMING]** and says so in the file.

**Theorem 2.7 (Abstract budget continuation, L0) [KERNEL, 2026-09-12]**
`SGC.Bridge.AbstractBKM.norm_le_exp_budget`. In any real normed space, if
`x : R -> E` has right derivative `x'` on `[0,T)` with `||x'(t)|| <= W(t) ||x(t)||`
for continuous `W`, then `||x(t)|| <= exp(int_0^t W) ||x(0)||`. Corollaries:
`bounded_of_budget_le` (finite budget => bounded evolution) and
`exists_budget_gt_of_norm_gt` (a norm excursion past `e^M ||x(0)||` forces the budget
past `M`). Proof: Mathlib's fencing lemma with the barrier
`exp(int W)(||x0|| + eps e^t)`, then `eps -> 0`.

---

## 3. The first axis: computation in fluids (Miranda - Moore) and the `epsilon = 0` pole

### 3.1 What is known **[EXTERNAL]**

Moore (1990-91) introduced generalized shifts on `A^Z` and showed they simulate
Turing machines, making basic questions about smooth dynamical systems undecidable.
Cardona, Miranda, Peralta-Salas, and Presas (PNAS 2021) embedded such shifts as
return maps of steady Euler flows on `S^3` via the contact mirror (Etnyre - Ghrist:
Beltrami fields are Reeb fields), producing Turing-complete steady Euler flows in
dimension 3; Dyhr, Gonzalez-Prieto, Miranda, Peralta-Salas (2026) extended this to
stationary Navier-Stokes states for any viscosity on manifolds carrying a
nowhere-vanishing harmonic field, with a generally deformed metric and Hodge-Laplacian
viscosity (the hypothesis is stronger than `H^1 != 0`). The
damped Beltrami flow `u(.,t) = M X0 e^{-nu t}` simulates the same computation with
total simulated-time budget `M/nu` (PNAS 2021, pp. 8-9).

### 3.2 SGC's reading

What SGC has formalized on this axis is Theorem 2.5 in its re-scoped form: a
*Bernoulli* shift tower with zero lumpability defect at every depth. This is a
statement about i.i.d.-input symbolic dynamics, not about Moore's machines; the
inference "therefore computation lives at `epsilon = 0`" made in v0.1 is withdrawn. Two
facts survive: exact lumpability gives an infinite validity horizon for *that* tower
(`exact_forecast_of_defect_zero` is the general form), and the `HaltingCompiler`
result (Theorem 2.4) is independent of the tower. The correct SGC object for a
deterministic generalized shift is open (a Markov partition or sofic coding is not an
automatic repair - external review). We keep the phrase **sealed-crystal pole** for
`epsilon = 0` as a name for exact closure, not as a claim about where computation lives. Two finite budgets bound it from the physical
side, both kernel-proven at the identity level: viscosity cuts simulated time to
`1/nu` (`viscous_time_budget`), and a nonzero lumpability defect cuts it to
`1/(nu epsilon)` (`damped_validity_budget`; the positivity of `epsilon` is an
interpretive hypothesis the proof does not use - recorded in our repair ledger).

The undecidability results (Theorem 2.4) are of the same family as Moore's: a global
property of a dynamical object (a curvature bound; a trajectory's fate) is
`Pi^0_1`-hard because a compiler places a marker at the halting step. The SGC
contribution here is not a new undecidable problem but a **reusable, kernel-checked
compiler template**: a marker-parameterized gadget lemma plus a bridge to Mathlib's
`TM0` and `PFun.fix` semantics, so that the reduction is a theorem rather than a
sketch.

### 3.3 What this axis does not say

It says nothing about singularities. The flows are steady or stationary; the
computation is eternal precisely because nothing collapses. The Buckmaster - Alpoge and
OpenAI constructions neither use nor imply computational universality. The SGC
dictionary B1-B7 is neither confirmed nor refuted by them.

---

## 4. The second axis: regularity and the continuation budget

### 4.1 Beale - Kato - Majda **[EXTERNAL]**

A smooth 3D Euler solution on `[0,T*)` extends past `T*` iff
`int_0^{T*} ||omega(t)||_Linf dt < inf`. Blowup therefore *requires* divergence of the
vorticity budget. The Euler artifact of 2026-09-08 proves this divergence for a
concrete datum.

### 4.2 The three budgets are three objects

| Quantity | Meaning | Status |
|---|---|---|
| `1/nu` | attenuation scale of a damped computational carrier | [KERNEL] identity, [FRAMING] interpretation |
| `int_0^T ||omega||_Linf dt` | Euler regularity-continuation budget | [EXTERNAL] target |
| `int_0^T D_pi(t) dt` | SGC closure-leakage / validity-horizon budget | [FRAMING]: Theorem 2.7 bounds a norm under a *given* differential inequality; identifying its density `W` with any closure defect requires a further inequality that is not proved |

They share a name and a shape - a scalar density whose integral must stay finite for a
description to continue - and nothing else has been proved.

### 4.3 The ladder, with named obligations

- **L0 (done).** Theorem 2.7. Any real normed space, time-dependent `W`. Open at L0:
  continuation via Picard - Lindelof (maximal-solution API), and replacing the
  constant `1` in `||x'|| <= W ||x||` by the BKM log-interpolation
  `||grad u||_inf <~ ||omega||_inf (1 + log^+(||u||_{H^s} / ||omega||_inf))`.
- **L1 (the SGC theorem).** Spectral Galerkin Navier-Stokes on `T^3` with projector
  `P_N` onto `|k| <= N`. Obligation: define `D_{pi,N}` and prove a uniform-in-`N`
  relation between it and a continuum regularity budget. Section 6.1 proposes the
  definition and Section 6.1' explains why the budget must be a *scale-transfer*
  quantity (Cheskidov - Shvydkoy's determining wavenumber), not `||omega||_inf`
  directly: vorticity does not lower-bound the defect.
- **L1' (type alignment).** State SGC-side continuum targets in the exact Mathlib
  conventions of the public challenge file (`fderiv` trace for divergence,
  `derivWithin (Ici 0)` in time, the same smoothness / decay / energy predicates) so
  that a future limit theorem has a matching endpoint type. Deferred until L1 needs
  it; a structure with no theorem behind it is a definition-cone item, not progress.
- **L2.** Uniform estimates and the limit `u_N -> u`: Sobolev regularity, commutator
  estimates, compactness, pressure. The 2026-09-08 Euler development contains modules
  whose names match this need (`BoundedMildContinuation`, `CylinderSobolev*`,
  `CompactVorticityContradiction`, `ClassicalBridge`); reuse is an inventory
  question, not an assumption.
- **L3.** `int_0^T D_pi < inf => int_0^T ||omega||_inf < inf => continuation`, under
  explicit hypotheses; the forced viscous analogue uses its own norms.

---

## 5. The two horizons

The unifying claim of this paper is **[FRAMING]**, stated so it can be attacked:

> A reduced description of a dynamical system can fail in two independent ways. It
> can fail *horizontally*: the coarse law stops tracking the projected fine dynamics
> because leakage accumulates (validity horizon `T* ~ 1/epsilon`, Theorems 2.1-2.2).
> It can fail *vertically*: the fine description itself ceases to exist because a
> regularity budget is spent (continuation budget `int W`, Theorem 2.7, BKM).

The Miranda - Moore axis concerns steady or stationary flows: nothing leaks from the
symbolic layer in the constructions, but a nonzero steady field still accrues
`T ||omega||_inf` of BKM budget over time `T` - stationarity does not make the density
zero (v0.1 said otherwise; corrected). The blowup axis concerns flows that spend a
continuation budget in finite time by collapsing scale. v0.1 argued this "cannot happen
while any fixed coarse description remains valid"; that is false for bounded energy
(Section 6.1'''), and the two axes are now presented as *distinct*, not as two ends of
one phase diagram.

Both are *horizon theorems of the same logical shape*, "finite budget implies bounded
evolution, excursion implies budget spent", which is why one Lean module (Theorem 2.7)
serves both and why SGC's existing Kernel-Horizon architecture was the natural
habitat for L0.

---

## 6. Novel ideas arising from the approach

### 6.1 The lumpability defect of Fourier truncation is the spectral energy flux **[CONJECTURE, definitional core is elementary]**

Take `P = P_N` (Fourier truncation) as the SGC coarse projector on Galerkin
Navier-Stokes, and the nonlinear analogue of `L` to be the vector field
`F(u) = -P(u . grad)u + nu Laplacian u + f` (Leray projector `P`). The SGC defect is the
part of the fine dynamics that leaves the coarse subspace when started inside it:

```
D_N(u) := (I - P_N) F(P_N u)  =  -(I - P_N) P (P_N u . grad) P_N u .
```

Its `L^2` pairing with the fine field is *related to* the **energy flux across the
cutoff `N`** (`Pi_N`), but the exact flux identity contains a further term, and a vector
residual norm is not a signed scalar flux (v0.1 said "exactly"; corrected). v0.1 then
read the Kernel-Horizon theorem as "validity horizon inverse in the flux through `N`";
that reading is withdrawn in 6.1''. A finite-time singularity was described in v0.1 as
the event in which flux reaches every finite `N` in
finite time, so that **every finite-`N` validity horizon closes before `T*`** - a
statement about a family of coarse descriptions, not about the fine solution alone. We
propose this as the L1 definition of `D_{pi,N}`.

### 6.1'' Leakage versus re-entry: a reviewer's correction **[elementary; changes the L1 object]**

An external reviewer (2026-09-12) pointed out that 6.1 as first written used the wrong
block. The defect `D_N(u) = (I - P_N) F(P_N u)` measures *leakage*: resolved modes
generating unresolved ones (the low-to-high flux). But the error of the coarse
description, `P_N u(t) - u_N(t)`, is driven by *re-entry*: unresolved modes feeding back
into the resolved ones. Writing `B(u,u) = P (u . grad) u`, the Duhamel identity for the
Galerkin error has as its forcing term

```
C_N(u) := P_N B(u,u) - B(P_N u, P_N u)  =  P_N [ B(u,u) - B(P_N u, P_N u) ] ,
```

which vanishes when `(I - P_N) u = 0` and is otherwise the **subgrid-scale closure
term** of large-eddy simulation - literally the closure problem of turbulence.

SGC already knows this distinction. In the linear theory the two blocks are
`D = (I - Pi) L Pi` (leakage, lower-left) and `R = Pi L (I - Pi)` (re-entry, upper-right);
the Kernel Horizon theorem (2.1) is stated with the closure *commutator* `C_T`, i.e. the
re-entry block, and the continuous-time bound (2.2) controls the error by `||D||` only
because for block-constant data the high-mode part is itself generated by leakage
(`DefectHorizonBridge` Section (iv), the "vertical companion") and because for
`pi`-self-adjoint `L` the two blocks are adjoint with equal norm. Neither mechanism
survives the nonlinearity unchanged: unresolved modes have their own dynamics
(`(I - P_N) B(u,u)` includes high-high interactions, the cascade), and there is no
adjointness identity between `C_N` and the flux.

Consequences for the program:

- The L1 object is `C_N`, the re-entry / closure term, not the flux `D_N`. The flux
  remains the natural *vertical* quantity (how fast the unresolved reservoir is fed) and
  the two are linked exactly as in `DefectHorizonBridge` (iv): error is driven by
  re-entry, whose source is leakage plus the unresolved modes' own dynamics.
- The Beltrami check survives: for a Beltrami eigenfield on `T^3` (`|k| = lambda`, e.g.
  ABC flows) `B(u,u) = 0` and `P_N u in {0, u}`, so `C_N(u) = 0` for every `N`.
- Conjecture 6.2 should be read with `C_N` in place of `D_N`: BKM divergence forces
  unbounded re-entry at every fixed scale. This is the sharper and more natural form -
  "no fixed resolution stays closed through a singularity".
- The reviewer question Q1 in `REVIEWER-COMMISSION.md` is restated accordingly.

### 6.1' The Beltrami check, and why the budget is not `||omega||_inf` **[elementary, KERNEL-ready]**

For a Beltrami field with *constant* `lambda` on the flat torus, `(u . grad) u =
grad(|u|^2 / 2)`, so the Leray-projected nonlinearity vanishes; `D_N(u) = 0` for every
`N` then requires that truncation preserve the Beltrami property (a curl-commuting
cutoff, as for Fourier truncation of an eigenfield). A manifold or contact realization
is not automatically a flat Fourier realization. The
Turing-complete steady Euler flows of Cardona - Miranda - Peralta-Salas are Beltrami.
Hence the fluids that compute sit *exactly* at the `epsilon = 0` pole of Theorem 2.5 -
a consistency check between the two axes that we did not design and that should be
made a kernel-checked lemma (the identity is a two-line vector calculus fact once the
Galerkin setting is formalized).

The same fact corrects a natural but wrong L1 target: Beltrami fields have arbitrary
vorticity and zero defect, so no inequality `D_N >= c ||omega_N||_inf - r_N` can hold.
Vorticity measures local rotation (stretching is `(omega . grad) u`); the defect
measures transfer across scale. Cheskidov - Shvydkoy's dissipation wavenumber
`Lambda(t)` **[EXTERNAL, arXiv:1102.1944, confirmed by review]**: `Lambda in L^1`
always (Lemma 3.1); `Lambda in L^{5/2}` implies regularity unconditionally (Theorem
3.2); the `Lambda in L^2` criterion (Corollary 3.4) additionally requires
`u in L^inf B^{-1}_{inf,inf}`; and different determining cutoffs are different objects
and must be treated separately. v0.1's sentence "their criterion `int Lambda^2 < inf`"
was imprecise. No equivalence between a wavenumber criterion, a defect norm, and an
approximation horizon has been proved, and none is asserted below.

### 6.1''' Bounded energy bounds every fixed-resolution quantity; the residual theorem **[KERNEL + reviewer correction]**

The same reviewer observed that on `T^3` the `k`-th Fourier coefficient of `(u . grad) u`
is `sum_{p+q=k} (u_p . iq) u_q`, hence bounded by `|k| ||u||_{L^2}^2`. So a bounded
kinetic energy `E` gives `||C_N(u)|| <~ N E` **at every fixed `N`, for all time,
through a finite-energy singularity**. This is exactly the regime of the 2026
Navier-Stokes construction (bounded energy, unbounded `L^inf`). Consequence: no
fixed-resolution quantity - neither the flux `D_N` nor the closure term `C_N` -
diverges at such a blowup. What escapes to infinity is the *resolution required* for a
given tolerance, not any observable at a fixed resolution. Conjecture 6.2 as stated in
v0.1 and v0.1.2 is therefore **false**, and is retracted below.

The reviewer also exhibited a smooth unforced flow with zero leakage defect and nonzero
projected Galerkin error, and prescribed the correct replacement: *a residual-controlled
error theorem, not a scalar-flux theorem*. We agree, and it is now kernel-checked:

**Theorem 2.8 (Residual Horizon) [KERNEL, 2026-09-12]**
`SGC.Bridge.ResidualHorizon.residual_horizon`. Let `v` be a coarse law, Lipschitz with
constant `K` on a region, `g` an exact coarse trajectory and `f` any trajectory in the
region with residual `||f' - v(f)|| <= eps` and `f 0 = g 0`. Then
`dist (f t) (g t) <= eps (e^{Kt} - 1) / K` on `[0, T]` (`residual_horizon_explicit`);
zero residual forces `f = g` (`exact_tracking_of_zero_residual`, the nonlinear
`epsilon = 0` pole); and a residual budget within tolerance gives a validity horizon of at
least `T` (`within_tolerance_of_residual_small`). Proof: Mathlib's
`dist_le_of_approx_trajectories_ODE_of_mem`. For Galerkin Navier-Stokes, `f = P_N u`,
`v` the Galerkin field, and the residual *is* `C_N(u)`. The theorem is a fixed-`N`
statement: `K = K_N` grows with `N`.

This reshapes the ladder. L1 is no longer "bound the error by the flux"; it is
"bound the residual `C_N(u)` along solutions" - the closure problem in its honest form -
and "control `K_N` and the accumulated residual uniformly enough that the resolution
required for tolerance `eta`, call it `N_eta(t)`, is the object whose escape to infinity
characterizes breakdown". That object is the determining wavenumber of 6.1'.

### 6.2 No renormalization-transparent blowup **[RETRACTED as stated; replaced]**

**Retracted (v0.1-v0.1.2):** "BKM divergence forces `limsup ||C_N(u(t))|| = inf` for
every fixed `N`." False by the energy bound of 6.1''' whenever kinetic energy is bounded,
which is the case of interest.

**Successor attempted in v0.1.3, also retracted:** "for every tolerance `eta`, the
minimal resolution `N_eta(t)` tracking `P_N u` within `eta` in `L^2` tends to infinity".
False: if both trajectories have `L^2` norm at most `M` then `||P_N u - v_N||_2 <= 2M`, so
sufficiently large tolerances never require increasing resolution (external review).
Any correct successor must use full-state approximation in a *continuation-controlling*
norm, and must distinguish computable validated endpoints from an ideal supremal one.

**What replaces it - the certified horizon [EXTERNAL, corollary of CCRT Theorem 8]:**
Chernyshenko - Constantin - Robinson - Titi prove that whenever a strong solution exists on
`[0, T]`, every sufficiently large Galerkin approximation passes their a posteriori test.
Define `T_N^CCRT` as the supremum of times passing the test; soundness plus eventual
success on every `T < T*` give `T_N^CCRT -> T*`. Monotonicity in `N` is not automatic
(a running maximum supplies it by construction). This is the rigorous form of a
*validity horizon* for fluids: a **specified certified guarantee**, not an intrinsic
phase boundary. SGC's contribution can only be formal verification and possibly sharper
computable constants, not the discovery of residual-based error control.

### 6.2 (original text, kept for the record)

Theorem 2.5 shows what eternal computation looks like in SGC terms: an exact
(`epsilon = 0`) tower at every scale. The blowup constructions show what a singularity
looks like: energy and vorticity concentrating on a core of radius `tau^{1/2} -> 0`.
These are incompatible at the level of coarse-grainings:

> **Conjecture (no renormalization-transparent blowup).** Let `u` be a smooth solution
> of 3D Euler or Navier-Stokes on `[0,T*)` with `int_0^{T*} ||omega||_inf dt = inf`.
> Then for every `N` the re-entry (closure) term satisfies
> `limsup_{t -> T*} ||C_N(u(t))|| = inf` (and a fortiori the flux `D_N` is unbounded);
> in particular no fixed finite coarse description is exactly lumpable on a
> neighbourhood of `T*`. (Stated with `D_N` in v0.1; corrected to `C_N` per 6.1''.)
>
> Equivalently in determining-wavenumber terms: BKM divergence forces
> `Lambda(t) -> inf` and every fixed-`N` validity horizon to close. If Cheskidov -
> Shvydkoy's criterion already implies this, 6.2 is a corollary and the novelty is
> only the coarse-graining reading; the reviewer question in Section 10 asks exactly
> this.

If true, this is a quantitative obstruction to the naive form of Tao's
"computational blowup" idea (build a fluid computer that programs its own
singularity): the computation, which (v0.1 asserted, without proof) requires `epsilon = 0` transparency across the
scales it uses, must *terminate* before the singularity, because the singularity
destroys transparency at every scale. It does not obstruct a computer that runs for a
finite time and then hands off to a purely analytic collapse - which is, in effect, what
the 2026 constructions do without any computer at all. The conjecture is stated so that
a Galerkin-level version (`||D_N(u_N(t))||` along Galerkin solutions, uniform in `N`)
is an L1/L2 theorem candidate.

### 6.3 A kernel-checked template for Pi^0_1-hardness of global budgets **[CONJECTURE, method KERNEL]**

Theorem 2.4's compiler places a marker at the halting step and converts a global
geometric bound into non-halting. The same template applies to any *global budget*
over a computably parameterized family. In particular:

> **Proposal.** For a computable family of finite-dimensional quadratic ODEs
> `x_H' = B(x_H, x_H) + A x_H` indexed by halting markers `H`, with budget density
> `W_H`, construct the family so that `int_0^inf W_H < inf <-> H` never fires. Then
> "finite continuation budget" is `Pi^0_1`-hard on the family, kernel-checkably,
> using `HaltingCompiler` unchanged.

The artificial version (marker enters `W_H` directly) is easy and uninteresting; the
interesting version makes `W_H` the honest Galerkin vorticity budget of a machine
embedded through the shift tower of Theorem 2.5. That would be a discrete,
kernel-checked cousin of the Cardona - Miranda - Peralta-Salas undecidability of Euler
trajectories, now for *budgets* rather than *reachability*, and would connect the two
axes of this paper by a theorem rather than an analogy.

### 6.4 Curvature as a regularity proxy for the linear part **[FRAMING, speculative]**

The viscous term is a Laplacian, whose discrete Bakry-Emery curvature controls gradient
bounds (`CD(rho, inf)` gives `Gamma(P_t f) <= e^{-2 rho t} P_t Gamma(f)`). Theorem 2.3
shows such bounds descend along exact quotients. The nonlinearity destroys curvature;
one can define a **curvature-deficit density** - the amount by which `Gamma_2` fails the
`CD` inequality along the flow - as a third candidate budget. We have no theorem and no
conjecture sharp enough to state; we record the direction because SGC already has the
Gamma-calculus kernel-checked and it is unusual to have curvature, lumpability, and
computability in one library.

### 6.5 Receipt discipline as a research contribution **[METHOD]**

The week of 2026-09-08 produced 2.3 million lines of machine-generated Lean and one
credit dispute. A kernel-checked proof settles logic, not modelling: a theorem can be
axiom-clean and still be about the wrong definition, a weakened statement, or a claim
its surrounding prose overstates. We built `lean-triage` to make the *definition
cone*, the *verbatim kernel statement*, the *witnesses* (a tactic that derives `False`
from the hypotheses; an empty binder type), and the *human claim map* first-class,
with every finding labelled kernel / witness / heuristic / attestation / process and a
receipt that lists what did *not* run. Dogfooding it on our own library found stale
citations and an interpretation-only hypothesis (`_h_eps` above). The point for this
paper is methodological: every declaration named here has a triage receipt, and every
sentence not backed by one is labelled.

---

## 7. What we do not claim

1. Any result about Clay alternatives A or B.
2. That SGC predicts, explains, or is confirmed by the 2026-09-08 constructions.
3. That the continuum dictionary of `DiscreteFluidDynamics` is a theorem.
4. That `1/nu`, the BKM budget, and the SGC defect budget are the same object.
5. That the external Lean artifact has been independently replayed by us.
6. That the conjectures of Section 6 are more than precisely stated targets.
7. That the mathematics of Theorem 2.3 is new (it is Pedrotti - Salez); the
   formalization and the witness are what is ours.
8. That `CantorShiftTower` formalizes Moore's generalized shifts or a Turing simulation.
9. That residual-controlled a posteriori error control for Galerkin Navier-Stokes is
   new (Morosi - Pizzocchero, arXiv:1104.3832, eq. (6.20), (4.24)-(4.27), Section 7;
   Chernyshenko - Constantin - Robinson - Titi, arXiv:math/0607181, Theorems 3, 8).
10. That any of `D_N`, `R_N`, `r_N`, `Pi_N`, a determining wavenumber, or a certified
    interval is equivalent to another; they are distinct objects and will be declared
    separately.
11. That a monotone "phase" quantity exists: time reversal excludes sign-even
    instantaneous monotone functionals for unforced Euler; stationarity excludes
    strictly decreasing averaged ones; deterministic Galerkin evolution has zero
    carre-du-champ even with viscosity.
12. That an invariant measure yields an autonomous finite-state Markov law: it yields a
    transition matrix with the right stationary law, whose powers need not be the
    multi-step statistics (Theorem 2.9's regression test).

---

## 8. Method: how this paper was produced and how it should be read

Claims labelled **[KERNEL]** are checked by the Lean 4 kernel (toolchain 4.25.2,
Mathlib pinned) with closure `propext, Classical.choice, Quot.sound`, as recorded by
`lean-triage` receipts (verbatim statement + SHA-256, axiom closure with origin,
unused-hypothesis check, definition cone, budgeted vacuity/triviality witnesses).
Claims about the external artifact rest on *reading* its public source; building an
untrusted Lean project executes arbitrary code (`lakefile`, macros, `extern`), so we
did not, and our threat model says when and how one should. Numbers quoted about the
external repositories (file counts, toolchains) are from the public tree and third-party
audits, not from our own build.

---

## 9. Claim map

| Declaration | Module | Establishes | Does not establish |
|---|---|---|---|
| `kernel_closure_error_le` | `Renormalization.KernelHorizon` | `||T^n K - K T-hat^n|| <= n ||C_T||` | tightness; continuum limit |
| `defect_horizon_bound` | `Bridge.DefectHorizonBridge` | explicit `O(t epsilon e^{...})` closure bound | anything about PDEs |
| `RicciCurvatureBound_quotient` | `Renormalization.CurvatureQuotient` | `CD(rho,inf)` descends along exact quotients | novelty of the mathematics (Pedrotti-Salez) |
| `cd0_compiled_iff` | `Bridge.HaltingCompiler` | global `CD(0,inf)` on compiled family <-> non-halting | undecidability of any fluid question |
| `shiftTower_defect_zero` | `Bridge.CantorShiftTower` | Bernoulli fresh-symbol shift kernels are exactly lumpable at every depth | Moore's generalized shifts; Turing simulation; any fluid realization |
| `stationary_iff_current_divergence_free` et al. | `Bridge.DiscreteFluidDynamics` | finite-state current/cycle/lift facts | the continuum dictionary |
| `viscous_time_budget`, `damped_validity_budget` | same | `int e^{-nu t} = 1/nu`; product identity | that `epsilon > 0` is needed (it is not used) |
| `norm_le_exp_budget`, `bounded_of_budget_le`, `exists_budget_gt_of_norm_gt` | `Bridge.AbstractBKM` | time-dependent Gronwall budget theorems in a normed space | BKM; anything about Euler/NS |
| `residual_horizon`, `exact_tracking_of_zero_residual` | `Bridge.ResidualHorizon` | homogeneous-Lipschitz residual-controlled tracking (wrapper of Mathlib) | the inhomogeneous energy estimate; any bound on a fluid residual |
| `statistical_forecast_horizon`, `fourCycle_K2_ne_K1_sq` | `Bridge.StatisticalHorizon` | `||P U^m P - A^m P|| <= m delta`; averaged one-step statistics do not compose | that any fluid's invariant measure has small `delta`; a curvature theory |
| `navier_stokes_breakdown_R3` (external) | `openai/NavierStokesAndEuler` | Clay (C), self-assessed, three axioms | replay by us; Clay (A)/(B) |

---

## 10. Roadmap and invitation

1. **L1 definition and first estimate** (months): define `D_N` as in 6.1 on spectral
   Galerkin Navier-Stokes on `T^3`; prove the flux identity kernel-checkably; attempt
   `||D_N|| <= C ||omega_N||_inf ||u_N||_{H^s}`-type bounds uniform in `N`.
2. **Read-only inventory** of the external Euler development's local-existence and
   Sobolev modules; decide import vs re-prove for L2.
3. **Sandboxed replay** of the external artifact with `lean-triage` and Comparator once
   our isolated-execution recipe exists; until then our stance is "read, not replayed".
4. **Conjecture 6.2** at Galerkin level as an L1/L2 target; **Proposal 6.3** as a
   self-contained discrete theorem reusing `HaltingCompiler`.
5. One quiet external technical review of this document focused on false reassurance
   and duplication of existing practice - not public engagement - before any wider
   circulation.

**Reviewer questions (v0.1).** (1) Is the defect of 6.1 the flux fluid dynamicists
mean? (2) Is 6.2 already known in some form? (3) The decisive one for L1: *Given that
Beltrami fields have zero Leray-projected nonlinearity (so the truncation defect
vanishes for all `N` while vorticity is arbitrary), is the right continuum partner of
the SGC validity horizon the Cheskidov - Shvydkoy determining wavenumber `Lambda(t)` -
specifically, is it known, false, or open that for spectral Galerkin truncation at
`N >= Lambda(t)` the defect `||(I - P_N) P (u_N . grad) u_N||` is bounded above and
below by the flux `Pi_N` with constants uniform in `N`, so that `int_0^T Lambda(t)^2 dt`
(rather than `int ||omega||_inf dt`) is the budget an SGC-to-fluid L1 theorem should
target?*

We are looking for collaborators in three communities: fluid analysts who can tell us
whether 6.1's defect is the flux they mean and whether 6.2 is already known in some
form; computability theorists interested in kernel-checked `Pi^0_1` templates; and
formalizers who want to help build L1 against a public, comparator-checkable target.

---

## References (primary sources read; secondary marked)

- Beale, Kato, Majda, *Remarks on the breakdown of smooth solutions for the 3-D Euler
  equations*, Comm. Math. Phys. 94 (1984).
- Cardona, Miranda, Peralta-Salas, Presas, *Constructing Turing complete Euler flows in
  dimension 3*, PNAS 118 (2021).
- Cardona, Miranda, Peralta-Salas, *Turing universality of the incompressible Euler
  equations and a conjecture of Moore*, arXiv:2104.04356.
- Cordoba, Martinez-Zoroa, *Blow-up for the incompressible 3D Euler equations with
  uniform C^{1,1/2-eps} cap L^2 force*, arXiv:2309.08495; and with Zheng, arXiv:2410.22920.
- Cushing, Kamtue, Liu, Peyerimhoff, arXiv:2102.08687.
- Dyhr, Gonzalez-Prieto, Miranda, Peralta-Salas, PNAS Nexus 5:5 (2026), arXiv:2507.07696.
- Etnyre, Ghrist, *Contact topology and hydrodynamics I*, Nonlinearity 13 (2000).
- Fefferman, *Existence and smoothness of the Navier-Stokes equation*, Clay (2000).
- Mitsumatsu, Peralta-Salas, Slobodeanu, arXiv:2311.15833.
- Moore, *Unpredictability and undecidability in dynamical systems*, PRL 64 (1990);
  *Generalized shifts*, Nonlinearity 4 (1991).
- OpenAI, *Finite time blowup for Navier-Stokes*; *Finite time blowup for the Euler
  equation*; `github.com/openai/NavierStokesAndEuler` (2026-09-08). Self-assessed.
- Pedrotti, Salez, *A new cutoff criterion for non-negatively curved chains*,
  arXiv:2501.13079.
- Morosi, Pizzocchero, *On approximate solutions of the incompressible Euler and
  Navier-Stokes equations*, arXiv:1104.3832 (eq. 6.20; 4.24-4.27; Section 7).
- Chernyshenko, Constantin, Robinson, Titi, *A posteriori regularity of the
  three-dimensional Navier-Stokes equations from numerical computations*,
  arXiv:math/0607181 (Theorems 3, 8; Corollary 5).
- Cheskidov, Shvydkoy, *A unified approach to regularity problems for the 3D
  Navier-Stokes and Euler equations: the use of Kolmogorov's dissipation range*,
  arXiv:1102.1944 (Lemma 3.1, Theorem 3.2, Corollary 3.4).
- Cheskidov, Dai, Kavlie, *Determining modes for the 3D Navier-Stokes equations*,
  arXiv:1507.05908.
- Tao, *Finite time blowup for an averaged three-dimensional Navier-Stokes equation*,
  JAMS 29 (2016).
- Buckmaster, Alpoge, `tristanbuckmaster/fluid_lean` (2026-09-08) - secondary, via
  press audit; not read by us.
- SGC Lean library `sgc-lean` (this project), modules as named; `lean-triage` v0.2.1.

---

## Change log

- **v0.1 (2026-09-12).** Initial. Conjecture 6.2 (fixed-cutoff collapse); defect identified
  with energy flux; `CantorShiftTower` described as Moore's shift.
- **v0.1.1.** Beltrami check; determining-wavenumber budget; third reviewer question.
- **v0.1.2.** Reviewer correction: error is driven by re-entry `R_N`, not leakage `D_N`
  (6.1'').
- **v0.1.3.** Reviewer correction: bounded energy bounds every fixed-cutoff quantity;
  6.2 retracted; Residual Horizon theorem (2.8) added.
- **v0.2 (2026-09-13).** Second review applied: abstract rewritten without "iff"s;
  Theorem 2.5 re-scoped to the Bernoulli tower and the computation axis relabelled
  [FRAMING]; 3.1 hypothesis corrected; 4.2 row relabelled; Section 5 stationarity
  sentence corrected; 6.1 flux "exactly" withdrawn; 6.1' vorticity/stretching and
  Cheskidov - Shvydkoy hypotheses corrected; Beltrami claim restricted; 6.2 successor
  retracted with the `2M` argument and replaced by the CCRT certified horizon; Statistical
  Horizon theorem (2.9) added with the four-cycle regression test; non-claims 8-12 added;
  prior art (Morosi - Pizzocchero; CCRT) cited. Lean additions: `ResidualHorizon`,
  `StatisticalHorizon`; `CantorShiftTower` docstring re-scoped.
