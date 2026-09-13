# Certificates, Not Slogans: What a Day of Adversarial Review Did to the SGC Program

## Progress report and path forward for the SGC -> Miranda-Moore -> Navier-Stokes program

**Jason Shroyer** (SGC project), with drafting assistance. Version 0.1, 2026-09-13.
Companion to *Two Horizons* (v0.2, 2026-09-12/13). Same labelling discipline:
**[KERNEL]** kernel-checked, declaration named; **[EXTERNAL]** cited; **[FRAMING]**
analogy we have not proved; **[CONJECTURE]** precise open target; **[RETRACTED]** a
claim we made and withdrew, with the reason. Claim map in Section 8.

---

### Abstract

Yesterday's paper proposed two horizon functionals - a coarse-graining validity horizon
and a regularity continuation budget - and conjectured that they collide in a fluid
computer that tries to compute its own singularity. Today three rounds of adversarial
review and a multi-agent critique tested that program against the primary literature
and against the Lean definitions themselves. The result is not a retreat but a change of
kind: every claim that connected SGC to fluids by *analogy* was either falsified,
re-scoped, or converted into a *certificate* - a theorem whose hypotheses name exactly
the semantic, approximation, and physical obligations that remain. Four new kernel-
checked modules were added (`StatisticalHorizon`, `DeterministicKernels`,
`ResidualHorizon`, `TerminalDecoding`, 250+ declarations, all with closure in the three
standard axioms). The central discovery of the day is negative and useful: the
"paradox filter" - a scale-cascading computer cannot both copy its program and hand
down its energy - is **false in the abstract** (a two-line theorem), so any obstruction
must be physical, and we now know precisely which physical hypotheses would have to be
supplied. We describe what this means for the Miranda-Moore axis (the tape is not the
cascade), for the Navier-Stokes axis (viscosity is not corruption), and for the program
(certificate-first, constraint ladder, statistical bridge).

---

## 1. Where we stood at dawn

*Two Horizons* v0.2 had already absorbed two review rounds: the Galerkin error is
driven by re-entry, not leakage; bounded energy bounds every fixed-cutoff quantity, so
the fixed-`N` collapse conjecture was dead; the shift tower is Bernoulli, not Moore;
residual-controlled a posteriori error control is prior art (Morosi-Pizzocchero, CCRT).
The morning began with a handwritten sketch that tried to rescue the big picture:

> finite Markov chains cannot compute (need countable state); `epsilon = 0` is where
> computation lives; viscosity taxes it; a singularity collapses scale; therefore a
> fluid computer melts before it computes its own blowup; prove this via undecidability
> of global curvature bounds; computation needs non-reversibility ("no palindromes").

Every clause of that sketch was tested today. Here is what survived.

## 2. The four axes, and what happened to each

### 2.1 Capacity **[settled]**

A finite global state set cannot realize unbounded computation. **Correction to the
sketch:** an infinite *alphabet* is not needed; Moore's generalized shifts use a finite
alphabet on a bi-infinite tape `A^Z` (unbounded coordinates supply the memory)
**[EXTERNAL, Moore 1991]**. SGC's only countable-state result is `HaltingCompiler` on
`Z` **[KERNEL]**, and the "beach glass" picture (a witnessable halt vs. a
co-semidecidable "no glass anywhere") is exactly `Pi^0_1` - the shape of a theorem we
already had, not a new one.

### 2.2 Directionality **[settled by theorem today]**

"A Turing-complete fluid cannot be a palindrome" became, after two corrections, exactly:

**Theorem (`DeterministicKernels.detailedBalance_iff_involutive`) [KERNEL].** For a
permutation `f` of a finite set with a strictly positive invariant measure `pi`, the
rate-one jump generator satisfies detailed balance iff `f (f x) = x` for all `x`.
**Corollary (`directed_dynamics_has_current_cycle`) [KERNEL].** Any orbit of length `> 2`
yields a directed cycle of strictly positive probability current.

**What it does not say [EXTERNAL, Bennett 1973].** Computation does not require
irreversibility: reversible universal Turing machines exist; Moore's shifts are
homeomorphisms; the CMPP flows are volume-preserving. The theorem is about *probability
current relative to an invariant measure* - a statistical arrow - not about dissipation,
logical irreversibility, or entropy production, and it does not characterize
computation. "Computation is a NESS" is therefore banned prose; "directed deterministic
dynamics is never a detailed-balance equilibrium" is the sentence.

### 2.3 Multiscale realization **[the axis the sketch got wrong]**

The sketch assumed the tape of a fluid computer lives in the degrees of freedom that
cascade. For the constructions that exist, it does not:

- **CMPP (PNAS 2021) [EXTERNAL].** The tape is a Cantor set of *Lagrangian addresses* in
  a Poincare section of one smooth Beltrami field. Fine tape cells are fine *positions*,
  not high *wavenumbers*. No cascade, no shrinking core; the computation runs forever.
  CMPP's own Remark 5.3 records the fragility of this encoding under perturbation and
  cites Bournez-Graca-Hainry.
- **Dyhr-Gonzalez-Prieto-Miranda-Peralta-Salas (2025/26) [EXTERNAL].** Turing-complete
  *stationary Navier-Stokes* fields for every `nu > 0`, on manifolds admitting a
  nowhere-vanishing harmonic 1-form, with a deformed metric. The carrier is harmonic:
  `Delta_g u = 0`, so `nu Delta_g u = 0` for every `nu`. **Positive viscosity does not
  imply active damping of the carrier.** Our earlier sentence "any positive viscosity
  blurs the Cantor tape" is **[RETRACTED]**.

The sketch's intuition returns *only* for Tao-type self-replicating designs, where the
machine at scale `n` builds a copy at scale `n/2` and hands it the energy. There the
question is real and open.

### 2.4 Regularity **[decoupled]**

A finite-energy singularity leaves every fixed-cutoff observable bounded. The only way a
singularity can threaten a computation is through the multiscale axis, and only if the
encoding's decoding margin or handoff depends on the quantity that loses control. Fixed-`N`
estimates cannot express that. The two axes are presented as distinct, not as two ends of
one phase diagram.

## 3. The paradox filter, tested

### 3.1 The bare toy is compatible **[KERNEL]**

Three agents independently predicted it; it took two lines to confirm.

**Theorem (`DeterministicKernels.bare_two_level_compatible`).** For any program map
`S : C -> C`, the step `handoff S (c, level) = (S c, fine)` has `Prod.fst` as an exact
factor map (`fst (handoff S x) = S (fst x)`) and transfers all activity to the fine level
(`activity` rises by `1`).

**Reading, with the reviewer's corrections.** `S` need not be injective, so this is exact
advancement of *declared semantics*, not recoverability of prior information; there is
no conserved energy, metric, perturbation model, or decoder margin. It is an algebraic
consistency check. **Its value is that it falsifies the strongest informal version of the
paradox filter before we invested in it.** Any obstruction must come from physical
constraints absent here: locality, incompressibility, an energy identity, bandwidth,
finite precision, noise, or a scale-normalized decoding margin.

### 3.2 Undecidability is not a shield **[settled]**

"Prove the obstruction by undecidability of a global Bakry-Emery bound" is a category
error. `cd0_compiled_iff` **[KERNEL]** says no algorithm decides the global bound on the
compiled family; it does not prevent any field from having any curvature. Ignorance is
not geometry. Two programs, kept apart forever: *hardness* (compiler template; a
legitimate Rice-type target: "whether this computable datum blows up is undecidable") and
*physical obstruction* (robustness under renormalization). Neither proves the other.

### 3.3 What the scaling test says **[elementary]**

Under the Navier-Stokes rescaling `ell -> q ell`, `a -> a/q`, `tau -> q^2 tau`, the
dimensionless viscous exposure `nu tau / ell^2` is invariant and packet energy scales by
`q`. Summable stage durations and energies are consistent; nothing forces stages to get
worse. Conversely a scale-independent loss factor `< 1` compounds over infinitely many
stages. **The missing estimate is genuinely missing**, and Tao's averaged model - which
keeps the energy identity and most estimates yet blows up - is the mandatory control: any
"universal" obstruction must be checked against it. Margins must follow their own norms
(positional tolerance scales by `q`, velocity `L^inf` by `q^{-1}`, `L^2` by `q^{1/2}`);
dividing everything by `ell` conflates them.

### 3.4 Two counterexamples that fix the definitions **[EXTERNAL review, elementary]**

1. **Robust readout now is not preservation of the computation.** A cylinder decoder
   reading coordinate `0` of a tape under `d(s,t) = sum 2^{-|i|-2} [s_i != t_i]` has
   uniform margin `1/4`, yet any positive perturbation budget can flip a distant bit that
   the shift later brings to the head. A per-read guarantee is not an all-run guarantee.
2. **Damping is not information loss.** The shear fields `u^{+/-} = +/- A e^{-nu k^2 t}
   sin(ky) e_x` solve unforced Navier-Stokes, decay, and remain distinct at every finite
   time: `d_TV(delta_{u^+}, delta_{u^-}) = 1`. Loss of distinguishability needs an
   observation, precision, or noise model; viscosity alone supplies none.

There is also a packing obstruction to the wrong definition: in a totally bounded space
an infinite family of codewords cannot have a uniform separation. Requiring the entire
infinite tape to be uniformly robust in a compact region would *assume* the impossibility
(Bournez-Graca-Hainry Thm 16 is about robust language acceptance under specific
hypotheses; their Thm 19 exhibits robust universal simulation on noncompact `R^6`).

## 4. What the reviews built instead: the certificate program

The decisive turn of the day. Rather than a physical no-go, the reviewer specified and we
formalized a **finite-state terminal decoding certificate** on top of the Kernel Horizon
theorem - a theorem whose hypotheses *are* the three obligations that every previous
slogan had conflated.

**Module `SGC.Bridge.TerminalDecoding` [KERNEL, 115 declarations, standard closure].**

- *Approximation.* `kernel_horizon_tv`: for any probability row `rho`,
  `tv(rho T^m J, rho J Q^m) <= min 1 (m c / 2)`, with `c = ||T J - J Q||_row` the same
  max-row `L^1` norm as `kernel_closure_error_le`; the sharper `||E_m||_row / 2`; and,
  when the coarse kernel has Dobrushin coefficient `delta < 1`, the uniform budget
  `c / (2 (1 - delta))` (`kernel_horizon_tv_uniform_mixing`), using only the zero row
  sums of the commutator. **No stationarity of `pi` anywhere.**
- *Semantics.* `kernel_terminal_reliability`: if a fixed (possibly randomized) decoder has
  reference error `<= beta_b` on each class and `beta_b + budget <= p_b`, then its actual
  error is `<= p_b` - **per class, no prior, no union**. The reference decoder's
  correctness is a hypothesis; closure cannot supply it.
- *Distinguishability.* `|D_obs - D_ref| <= eps_0 + eps_1`; both errors `<= p_b` forces
  `D_obs >= 1 - p_0 - p_1` (necessary, not sufficient); the aligned sandwich
  `max 0 (D_ref - 2 eps) <= D_obs <= D_full <= Gamma * D_in`, where the contraction
  `Gamma` is an **explicit hypothesis about the complete state** - never inferred from
  closure, positivity, or dissipation; `no_terminal_decoder_of_contraction`
  (`U < 1 - p_0 - p_1` rules out every decoder, randomized included);
  `iterated_tv_contraction` across changing state spaces.
- *Regressions, as theorems.* Exact closure with an erasing observation (`c = 0`,
  `D_obs = 0`, `D_full = 1`, no decoder both errors `< 1/2`) - kills "zero defect implies
  decodability". Average vs worst conditional error (`tv = 1/2`; equal-prior optimum
  `1/4`, randomized minimax `1/3`, deterministic `1/2`, all attained). Nonstationary
  weights with exact transfer. `swap` has Dobrushin `1`; `reset` has `0` and forgets both
  inputs in one step.

**The compatibility inequality.** Combining the certificates gives, for the same decoder
and experiment,

```
e_0^ref + e_1^ref + m c  >=  1 - D_in * prod_{j<m} theta_j .
```

Strong reference reliability, small closure error, and strong complete-channel
forgetting cannot all hold. This is elementary; its value is that it converts the whole
"computation vs. collapse" intuition into a statement with three named premises, any one
of which can be the false one.

**Two companions.** `StatisticalHorizon` **[KERNEL]**: `||P U^m P - A^m P|| <= m delta`
for a Koopman-type contraction and a projection - the Kernel Horizon on `L^2(mu)` - with
the four-cycle regression (`K_2 != K_1^2`: averaged one-step statistics do not compose).
`ResidualHorizon` **[KERNEL]**: residual-controlled tracking via Mathlib's approximate-
trajectories Gronwall, labelled as the homogeneous-Lipschitz form; the inhomogeneous
energy estimate is the correct next L1 target and is not claimed.

## 5. What this means for SGC

1. **SGC's finite-state theory is intact and sharper.** The Kernel Horizon theorem
   acquired an operational meaning (a decoding certificate) and a mixing refinement, both
   without stationarity. The statistical bridge has its horizon theorem and its first
   regression test. The deterministic-kernel lemmas connect six existing theorems.
2. **The bridge to fluids is now a specification, not an analogy.** L1 is
   `GalerkinResiduals` (four separate declarations `D_N, R_N, r_N, Pi_N`, the exact error
   equation, the trilinear cancellation, the `N^{5/2}` bound, the `M=3, N=1`
   counterexample as theorems) and the inhomogeneous comparison, cited to MP/CCRT.
3. **The validity horizon is a certified guarantee, not a phase boundary.** CCRT Theorem 8
   makes `T_N^CCRT -> T*` a corollary; monotonicity in `N` only as a running maximum.
4. **`pi`-weighting attaches to invariant measures, not trajectories** - but an invariant
   measure yields a transition matrix, not an autonomous coarse law (four-cycle); the
   statistical horizon quantifies exactly that gap.

## 6. What this means for Miranda-Moore

- The Bernoulli tower theorem stands, correctly named; the Moore identification is
  framing. The correct SGC object for a deterministic generalized shift is open (a Markov
  partition or sofic coding is not an automatic repair).
- The 2025 harmonic-carrier construction is a **mandatory consistency check**: any claimed
  obstruction must accommodate it or impose a hypothesis it fails. "Viscosity corrupts the
  tape" is dead; "does dissipation act on the degrees of freedom carrying the required
  logical distinctions?" is the question.
- Under any perturbation, CMPP's encoding is fragile by their own remark; robust
  computation lives on noncompact resources. Whether a *Lagrangian* encoding in a
  *time-dependent, nonzero-flux* flow can be robust is unresolved in both directions.

## 7. What this means for Navier-Stokes

- Nothing here touches Clay (A)/(B). The 2026-09-08 artifacts remain self-assessed,
  read-not-replayed, and orthogonal to the Miranda-Moore axis.
- Tao's blueprint is the only place the sketch's intuition has content, and there it is a
  precise open question about robust computation under indefinitely repeated physical
  rescaling: with decoders `P_n`, tolerance radii `delta_n` (scale-normalized as
  `delta_n / ell_n`), handoffs `R_n`, activity `E_n`, and simulation `S_n`, does the
  approximate commuting square `P_{n+1} o R_n o F_n ~ S_n o P_n` plus a transfer
  `E_{n+1} >= alpha E_n` force `inf_n delta_n / ell_n = 0`? The bare case says no. The
  first physical constraint that forces yes - if any - is the theorem.
- Any such theorem must survive Tao's averaged model or explicitly use structure it lacks
  (the vorticity formulation with differential rather than pseudodifferential operators).

## 8. Path forward

**Certificate first, constraint ladder second, continuum last.**

| Stage | Add | Deliverable | Status |
|---|---|---|---|
| 0 | nothing | `bare_two_level_compatible` | done [KERNEL] |
| C | terminal decoding certificate | `TerminalDecoding` | done [KERNEL] |
| 1 | positive scale-normalized decoder radius | compatible example or minimal obstruction | next |
| 2 | finite alphabet + local finite-radius update | does local symbolic refinement keep a uniform margin? | |
| 3 | fixed per-level bandwidth after rescaling | margin/bandwidth trade-off? | |
| 4 | contractive smoothing / noise model | quantitative upper bound on `delta_{n+1}` | |
| 5 | divergence-free Galerkin realization | does incompressibility or the energy identity change the answer? | L1 (`GalerkinResiduals`) |
| 6 | viscosity / dissipation | a physical lifetime or an impossibility, if justified | L2-L3 |

Rules adopted today, to be held to: the margin comes before bandwidth (an idealized real-
number encoding can hide infinite information in fragile distinctions); construct the
strongest compatible example at each stage before attempting a no-go; keep `D_N`, `R_N`,
`r_N`, `Pi_N`, determining wavenumbers, and certified intervals as distinct declarations;
keep hardness and physical obstruction in separate modules; ban the phrases "universal
paradox filter", "NS regularity by undecidability", "`epsilon = 0` towers are Moore
machines", and "computation is a NESS" without the Bennett caveat.

Process: independent replay of the branch (Gate 1); a sandbox recipe so the external
Navier-Stokes artifact can be triaged rather than read (Gate 3); the two lean-triage
false positives found today (hypotheses the *statement* depends on; compiler-generated
lemmas) are fixed and covered by the selftest.

## 9. Claim map (today's additions)

| Declaration | Module | Establishes | Does not establish |
|---|---|---|---|
| `detailedBalance_iff_involutive` | `DeterministicKernels` | detailed balance iff involution, deterministic finite kernels | that computation needs irreversibility |
| `directed_dynamics_has_current_cycle` | same | orbit `> 2` gives a positive-current cycle | thermodynamic NESS in the physical sense |
| `bare_two_level_compatible` | same | exact program factor map + total activity transfer are compatible | any physical statement; recoverability |
| `statistical_forecast_horizon`, `fourCycle_K2_ne_K1_sq` | `StatisticalHorizon` | `m delta` forecast bound; averaged statistics do not compose | a fluid instance; small `delta` for any measure |
| `residual_horizon`, `exact_tracking_of_zero_residual` | `ResidualHorizon` | homogeneous residual-controlled tracking | the inhomogeneous energy estimate |
| `kernel_horizon_tv`, `_sharp`, `_uniform_mixing` | `TerminalDecoding` | TV budgets `min 1 (mc/2)`, `||E_m||/2`, `c/(2(1-delta))` | anything at intermediate times |
| `kernel_terminal_reliability` | same | per-class error transfer given reference correctness | reference correctness |
| `joint_terminal_certificate`, `no_terminal_decoder_of_contraction` | same | sandwich and impossibility given an explicit full-state contraction | the contraction |
| `Regression.*` | same | the review's counterexamples as theorems | - |
| `cd0_compiled_iff` (existing) | `HaltingCompiler` | global `CD(0,inf)` on compiled family iff non-halting | any physical obstruction |

## 10. One paragraph for the record

The morning's sketch said: a fluid computer must keep its tape transparent across all
scales, a singularity collapses scale, so the computer melts before it computes its end.
By evening, every step had been replaced by something checkable: the tape of the fluids
that compute is Lagrangian, not spectral; viscosity does not touch a harmonic carrier;
the abstract compatibility of program-copying and energy-handoff is a two-line theorem;
undecidability constrains algorithms, not fields; directed dynamics has a current, not an
irreversibility requirement; and what remains of the intuition is a precise open question
about robust computation under repeated physical rescaling, together with a kernel-checked
certificate that names, as separate hypotheses, the three things any answer must supply -
what the computation is, how well the coarse model approximates it, and what the physics
does to the distinctions it needs. That is a smaller claim than yesterday's and a much
better place to stand.

---

## References (added today; see *Two Horizons* for the rest)

- Bennett, *Logical reversibility of computation*, IBM J. Res. Dev. 17 (1973).
- Bournez, Graca, Hainry, *Computation with perturbed dynamical systems*, J. Comput.
  Syst. Sci. 79 (2013), Defs. 7-12, Thms 16-19.
- Cardona, Miranda, Peralta-Salas, Presas, PNAS 118 (2021), Remark 5.3.
- Dyhr, Gonzalez-Prieto, Miranda, Peralta-Salas, *Turing complete Navier-Stokes steady
  states via cosymplectic geometry*, arXiv:2507.07696; PNAS Nexus 5:5 (2026).
- Graca, Campagnolo, Buescu, robust Turing simulation by analytic ODEs on `R^6`.
- Polyanskiy, Wu, strong data-processing inequalities and Dobrushin coefficients.
- Tao, *Finite time blowup for an averaged three-dimensional Navier-Stokes equation*,
  JAMS 29 (2016), and the accompanying discussion of structure the averaged model lacks.
- External review documents filed under `docs/reviews/` and `docs/specs/` on this branch.
