# Synthesis after the multi-agent review of the 2026-09-13 sketch

Purpose: settle the understanding and the path. Every line below is one of: **settled**
(theorem or refuted), **corrected** (a claim we withdraw, with the reason), **open** (a
precise question), or **decision**.

## 1. Four axes, kept apart

| Axis | Question | Status in SGC |
|---|---|---|
| Computational capacity | Does the state space support unbounded memory? | Finite `V` cannot. `HaltingCompiler` (on `Z`) is our only countable-state result. |
| Directionality | Is there a current that carries a computation forward? | **Settled today:** deterministic + positive invariant measure: detailed balance iff involution; any orbit of length > 2 is a NESS with a current cycle (`DeterministicKernels`). |
| Multiscale realization | Is logical information stored in degrees of freedom that cascade? | Depends on the machine: **no** for Moore/CMPP (tape = Lagrangian Cantor address in a Poincare section of one smooth Beltrami field); **yes** for Tao's self-replicating design. |
| Regularity / blowup | Does the PDE lose smoothness, and can that be linked to encoding loss? | Only via the multiscale axis, and only for Tao-type designs. No fixed-`N` quantity can express it (bounded energy). |

## 2. Corrections to the sketch (and to my first synthesis)

- **"Need an infinite alphabet."** Withdrawn. Moore's generalized shifts use a *finite*
  alphabet on a bi-infinite tape `A^Z`; unbounded memory comes from infinitely many tape
  coordinates. Finite alphabet + infinite support is cleaner for Lean. "Countable
  configuration space" is the correct requirement; "GCMS" bundled three different objects
  (countable-state chain, generalized shift with uncountable phase space, continuum PDE).
- **"The computer melts before it computes its singularity."** Withdrawn as a general
  claim. False for steady Miranda computers (no cascade, tape scale != Fourier scale,
  runs forever). Survives only as a *conditional* question about Tao-type designs
  (Section 4).
- **"Prove the obstruction via undecidability of a global curvature bound."** Category
  error, withdrawn. Undecidability is epistemic (no algorithm certifies), not ontic
  (the fluid is not prevented from anything). `cd0_compiled_iff` stands as a
  *hardness* result; it obstructs no dynamics. The beach-glass picture is the correct
  picture of `Pi^0_1`, and of a theorem we already have.
- **"Computation is a NESS" / "need non-reversibility."** Overstated in my first
  synthesis; corrected. Bennett 1973: reversible universal Turing machines exist; Moore's
  shifts are homeomorphisms; CMPP flows are volume-preserving. What is true and now
  proven: a *directed* deterministic dynamics (orbit length > 2) is never a
  detailed-balance equilibrium and carries a current cycle. That is a statement about
  probability current relative to an invariant measure - not about dissipation, logical
  irreversibility, or entropy production. Directed drift != irreversibility.
- **"Physical budget is exhausted."** Replace with a measurable quantity: required
  decoding precision / stability margin of the encoding at scale `n`, and prove it
  degenerates (or does not) under the proposed cascade.
- **"Infinite perfect data required to keep eps = 0 or blowup."** Not a theorem; it
  smuggles a continuum identification neither SGC nor CMPP has earned.

## 3. What got settled by theorem today

- `detailedBalance_iff_involutive`: palindrome = involution = no arrow. **[KERNEL]**
- `directed_dynamics_has_current_cycle`: directed deterministic dynamics is a NESS with a
  positive-current cycle. **[KERNEL]** (connects to `current_zero_iff_reversible`,
  `ness_has_current_cycle`, and the four-cycle of `StatisticalHorizon`).
- `bare_two_level_compatible`: the *bare* requirement "exact program preservation +
  definite energy transfer to the fine level" is jointly satisfiable. **[KERNEL]**
  Consequence: **the paradox-filter slogan is false in the only regime we can currently
  check.** Any obstruction must come from constraints absent in the abstract toy.
  Agent 1 predicted this; it took two lines to confirm, which is the point of writing
  the toy down before the intuition cools.

## 4. The one open question worth a program

**Robust computation under indefinitely repeated physical renormalization.**
For Tao-type designs, define at each level `n`: configurations `X_n`, program states
`C_n`, decoder `P_n`, tolerance radius `delta_n` (perturbations below `delta_n` do not
change the decoded symbol), dynamics `F_n`, handoff `R_n : X_n -> X_{n+1}`, activity
`E_n`, simulation `S_n : C_n -> C_{n+1}`. Require the approximate commuting square
`P_{n+1} o R_n o F_n ~ S_n o P_n`, the transfer `E_{n+1}(R_n x) >= alpha E_n(x)`, and a
non-collapse condition `delta_{n+1} >= Phi(delta_n)`. The candidate obstructions are:
`delta_{n+1}/delta_n -> 0` forced by exact simulation; super-exponentially small control
precision; energy transfer forcing an instability that destroys the margin; unavoidable
information loss in rescaling; error-correction overhead outgrowing resources.

`bare_two_level_compatible` says: with no `delta_n`, no locality, no bandwidth, no
noise, there is no obstruction. So the program is: add the physical constraints one at
a time (divergence-free, energy identity, fixed bandwidth per level, finite precision,
locality) and find the first one that forces `inf_n delta_n = 0` - or exhibit a uniformly
robust scheme, in which case the slogan is dead and the remaining hope is a continuum
constraint. Either outcome is a lemma; neither is a well.

Agent 3's nuance is worth keeping: for CMPP under *any* perturbation or `nu > 0`, the
Cantor tape blurs by advective diffusion (horizontal failure), and `1/nu` is the
relevant budget. That is the honest content of "viscosity taxes the child's lifetime".

## 5. Decisions

1. **Do not** generalize lumpability/horizons to countable `V` as the first move. The
   direct route is: symbolic model on `A^Z` or a Turing configuration space; finite-
   resolution decoder; scale-transfer operator; stable simulation or obstruction under
   quantitative hypotheses; PDE only after. Countable-state SGC is infrastructure to be
   built when the symbolic model needs it.
2. **Done:** involution lemma, current-cycle corollary, bare-toy compatibility.
3. **Next Lean item:** the two-level toy *with one physical constraint added* -
   a fixed per-level bandwidth (finite `C_n` of bounded size) and a decoder margin
   `delta_n` - as the first candidate for a genuine no-go. Formulate before proving;
   try to construct a counterexample first.
4. **Keep separate forever:** hardness/undecidability results (compiler template) and
   physical-obstruction results (robustness under renormalization). Neither proves the
   other.
5. **Public prose bans:** "universal paradox filter", "NS regularity by undecidability",
   "eps = 0 towers are Moore machines", "computation is a NESS" without the Bennett
   caveat.

## 6. One sentence

A machine that must both preserve a program under renormalization and hand a definite
energy flux to the next scale is being asked to be a factor map and a NESS on the same
step; in the abstract those two roles commute trivially (proved), so if there is an
obstruction it is physical, not logical - and finding the first physical constraint that
breaks the commutation is the program.
