# The Computation Axis, Rebuilt: Factor Maps, Exact Blocking, and What the Defect Measures

## Follow-up to *Certificates, Not Slogans* (same day, afternoon session)

**Jason Shroyer** (SGC project), with drafting assistance. Version 0.2, 2026-09-13
(v0.1 corrected the same evening after external review of `MachineCertificate`; the
corrections are marked **[CORRECTED]** and summarized in Section 5a).
Labels as before: **[KERNEL]** kernel-checked, declaration named; **[EXTERNAL]** cited;
**[FRAMING]** unproved analogy; **[CONJECTURE]** precise open target; **[RETRACTED]**.

---

### Abstract

The morning report ended with the computation axis of SGC relabelled from [KERNEL] to
[FRAMING]: the only formal object on that axis, the Bernoulli shift tower, does not
describe Moore's machines. This report records that the axis has been rebuilt on the
correct object in one afternoon, with three kernel-checked results and one regression
test. (1) *Temporal blocking of a deterministic computation is an exact coarse-graining*:
`(T_f)^b = T_{f^[b]}`, and on Mathlib's Turing machines `h` blocks of `b` steps is
`b*h` steps, with the block tower halting-faithful against Mathlib's own `Turing.eval`.
(2) *Exact lumpability of a deterministic dynamics is a factor map*:
`IsStronglyLumpable (T_f) P <-> (x ~ y -> f x ~ f y)`, so SGC's `epsilon = 0` pole is
literally the semiconjugacy that Moore and Cardona-Miranda-Peralta-Salas-Presas use to
encode a machine into a flow; under it the canonical `pi`-weighted coarse kernel *is* the
quotient machine and `pi` is gauge. (3) *Reading the tape is measured by the defect*: a
machine whose control flow depends on its tape has strictly positive measure-reentry
defect when coarse-grained by control state, for every reference measure. Together these
change what the program can honestly say: SGC is a theory in which the objects of
symbolic dynamics (factor maps, block codes, halting) appear as the exact case of a
quantitative theory of coarse-graining error, and the quantitative case measures exactly
what a coarse description of a computation must forget. We spell out the ramifications
for Moore/Miranda, for the 2025 complexity manuscript, and for the fluid bridge, and
state the next two theorems.

---

## 1. Why the axis had to be rebuilt

*Two Horizons* v0.1 wrote: "Moore's shift is renormalization-transparent [KERNEL]". The
reviewer read the definitions: `CantorShiftTower.shiftKernel` is a uniform fresh-symbol
(Bernoulli) kernel; its exact lumpability under deletion of the oldest symbol is a valid
theorem about i.i.d.-input symbolic dynamics and says nothing about a deterministic
generalized shift, finite-window rewriting, or a Turing simulation relation. v0.2
accepted this and relabelled the axis [FRAMING], leaving the question the reviewer posed
as Q2: *what is the correct SGC object for a deterministic generalized shift?*

The morning's multi-agent critique added the constraint that made the answer findable:
the right carrier of computation is a *deterministic map on configurations*, not a
stochastic kernel with an infinite alphabet. Once the object is a map, SGC's vocabulary
has to be tested against it directly.

## 2. The three results

### 2.1 Blocking is exact **[KERNEL, `SGC.Bridge.BlockRenormalization`]**

The 2025 manuscript *The Physical Basis of Computational Complexity* read the
Williams / Cook-Mertz simulation (`TIME[t] subset of SPACE[sqrt(t log t)]`) as a renormalization
flow: a time block is a coarse-graining step, the `b`-step simulation is the RG rule. Of
that reading, exactly this is a theorem:

- `detKernel_pow`: for `f : V -> V` on finite `V`, `(detKernel f)^b = detKernel (f^[b])`.
  The block map is the `b`-th power of the one-step kernel; the block-level Markov law is
  exact with **zero closure error**, for every `b`.
- `multistep_add`, `multistep_mul`: for any partial step `f : sigma -> Option sigma`
  (Mathlib's `TM0.step M`), `h` blocks of `b` steps is `b*h` steps. The Cook-Mertz node
  function composes exactly across levels.
- `halts_iff_block_halts`, `evalDom_iff_block_halts`: for `b >= 1`, the machine halts iff
  some block count yields `none`; the left side is Mathlib's `(Turing.eval f a).Dom`.

**Ramification.** Whatever a Williams-style block simulation costs in space, it is *not*
paying for approximation error between levels - that is zero. The cost is retained
state. This is the precise, honest content behind the manuscript's "local consolidation
cost vs global integration cost", and it relocates its Theorem 1 (`S >= Omega(1/lambda +
t lambda log C)`) to where it belongs: **[CONJECTURE]**, needing an adversary or
information argument that the manuscript does not supply (Cook-Mertz's `O(b)` is an
*upper* bound).

### 2.2 Exact lumpability is a factor map **[KERNEL, `SGC.Bridge.DeterministicLumpability`]**

```
detKernel_stronglyLumpable_iff :
  IsStronglyLumpable (detKernel f) P  <->  forall x y, P.rel x y -> P.rel (f x) (f y)
```

The right-hand side is `Descends f P`: `f` induces a map `quotMap f P` on `P.Quot` with
`quot_map o f = quotMap f P o quot_map`. That is the semiconjugacy / factor-map
condition of symbolic dynamics - the notion Moore (1991) uses to realize a Turing machine
as a generalized shift, and the notion CMPP (2021) use to encode the shift into the
return map of a Beltrami field on a Cantor transversal (`pi o Phi = sigma o pi`).

Consequences, each kernel-checked and each valid for *every* strictly positive reference
measure `pi`:

- `closureCommutator_detKernel_eq_zero_iff`, `defectSq_detKernel_eq_zero_iff`: the
  measure-reentry defect vanishes iff `f` descends. **SGC's `epsilon = 0` pole is the
  existence of a factor map.**
- `coarseGenerator_detKernel_eq`: under lumpability the canonical coarse kernel equals
  `detKernel (quotMap f P)`. **The renormalized machine is again a machine, and `pi` is
  gauge** - the Trinity-theorem phenomenon (the measure drops out at exact lumpability),
  now for computations.
- `eternal_closure_detKernel`: `T_f^n K = K T_{f-bar}^n` for all `n` - infinite validity
  horizon, correctly attributed to the factor map rather than to "computation".
- `Descends.iterate`, `quotMap_iterate`, `detKernel_pow_stronglyLumpable`: blocking
  commutes with quotienting. The temporal tower of 2.1 and the spatial quotient of 2.2 are
  one structure.

**Ramification.** Q2 is answered by theorem. Any deterministic generalized shift that is
a factor of a machine - Moore's construction - *is* an exactly lumpable SGC quotient, and
conversely. The computation axis can carry [KERNEL] again, on the right object.

### 2.3 Reading the tape is measured by the defect **[KERNEL, `Regression`]**

Two two-state, two-symbol machines on configurations `(control state, symbol under the
head)`, coarse-grained **by control state**:

- `oblivious` flips its state and ignores the symbol: exact, quotient is the state-flip
  machine, defect `0`.
- `reader` moves to the state named by the symbol it reads:
  `reader_defect_pos : 0 < defectSq (detKernel reader) byState pi` for every positive `pi`.

**Ramification.** This is the first inequality on the computation axis that involves an
actual machine, and it says the right thing: *a coarse description that discards the tape
must have positive defect whenever the control flow depends on the tape.* It also
explains, after the fact, why the Bernoulli tower had `epsilon = 0`: fresh i.i.d. symbols
carry no information the control ever needs. The tower was exactly lumpable *because* it
was not computing.

## 3. What this changes

### 3.1 For SGC as a theory

Before today, SGC's lumpability theory and symbolic dynamics were related by analogy.
Now they are related by an iff on the deterministic sector:

| Symbolic dynamics | SGC (deterministic kernels) | Declaration |
|---|---|---|
| factor map / semiconjugacy | exact strong lumpability | `detKernel_stronglyLumpable_iff` |
| quotient system `f-bar` | canonical coarse kernel (`pi` gauge) | `coarseGenerator_detKernel_eq` |
| block code (`f^[b]`) | `b`-th kernel power | `detKernel_pow` |
| halting | block tower reaches `none` | `evalDom_iff_block_halts` |
| "the quotient forgets something the dynamics uses" | `defectSq > 0` | `reader_defect_pos` |

The quantitative theory (Kernel Horizon, Statistical Horizon, Terminal Decoding) then
sits *around* this exact sector as its `epsilon > 0` deformation. That is a much stronger
structural claim than "SGC is like RG", and every row of the table is a theorem.

### 3.2 For Moore and Miranda

- The correct reading of CMPP in SGC terms is now available: their construction supplies
  a factor map from a Cantor transversal of a Beltrami flow onto Moore's generalized shift,
  which is itself a factor of a Turing machine. Each arrow is an exact SGC quotient in
  the sense of 2.2. What SGC adds is not the construction (theirs) but the *quantitative
  neighbourhood* of it: what happens to the horizon and the decoder when the factor map
  is only approximate - which is precisely the robustness question CMPP's Remark 5.3
  raises and Bournez-Graça-Hainry constrain.
- The 2025/26 harmonic-carrier Navier-Stokes result is untouched by all of this and
  remains the consistency check for any obstruction claim.

### 3.3 For the 2025 complexity manuscript

Its three components now have homes: block composition is 2.1 [KERNEL]; blanket
preservation by DPI is `Consolidation.RG_monotonicity` (existing, from the DPI axiom);
the space lower bound is [CONJECTURE], Stage 3 of the constraint ladder. The
"isomorphism" is a dictionary; the dictionary is now partly theorems. The manuscript's
retraction of its own `mu-eta`-block error is the same discipline we practised today.

### 3.4 For the fluid bridge

Nothing in this report touches Navier-Stokes regularity, and the morning's conclusions
stand: the paradox filter is false in the abstract; viscosity is not tape corruption;
the missing object is a physical contraction on the complete state. What today adds is
that the *symbolic* side of any future fluid-computation statement is now formal: if a
flow is claimed to compute, the claim is that a factor map exists (2.2) whose block
structure is exact (2.1); if the flow is perturbed, the claim degrades to a positive
defect (2.3) whose consequences for decoding are exactly `TerminalDecoding`'s three
hypotheses. The bridge is now typed at both ends.

## 4. What is not claimed

- No Turing simulation is exhibited. `Descends` is the *condition*; exhibiting `f`, `P`,
  and the simulation relation for a universal machine is Moore's theorem, not ours.
- No robustness under perturbation. A factor map is exact by definition; the
  perturbative theory is the `epsilon > 0` sector, and its decoding consequences require
  the semantic and contraction hypotheses of `TerminalDecoding`.
- No space lower bound. 2.1 shows approximation cost is zero; it does not bound retained
  state.
- Nothing about fluids beyond typing the symbolic end of the bridge.
- The Bernoulli tower remains a separate, correctly named object; today explains why it
  is exact, it does not rehabilitate the Moore identification.

## 5. The next two theorems

1. **Moore's factor map as a `Descends` instance [KERNEL target].** Take Mathlib's
   `TM0` on a *finite* tape window (so `V` is finite), the partition by (state, window
   contents relevant to the next `b` steps), and prove `Descends (f^[b]) P` - i.e. the
   `b`-step block map is exactly lumpable onto the coarse variables it actually reads.
   This is the honest formal content of "the TEP node function is well defined", and its
   failure outside the window is `reader_defect_pos` at scale. It also gives the first
   example in the tree where `defectSq` is computed on a machine as a function of window
   size: the quantitative shape of "how much tape must a coarse description keep?"
2. **The decoding certificate on a blocked machine [KERNEL target].** Combine 2.1 with
   `TerminalDecoding`: for a deterministic machine observed through a partition `P` with
   defect `c`, the terminal decoding budget after `h` blocks is `min 1 (h c / 2)`.

Both were done the same evening (`SGC.Bridge.MachineCertificate`), and the external
review of that module produced the corrections and the new theorem in Section 5a.

## 5a. Corrections after review of `MachineCertificate` **[CORRECTED]**

The reviewer found no error in the theorem statements and four overstatements in the
prose around them. All four are withdrawn here and in the module docstrings.

1. **"Deterministic quotients do not mix, so the coarse-graining error of a computation
   accumulates linearly."** Withdrawn. `mixing_budget_trivial_of_quotient_machine`
   assumes `Descends`, hence `c = 0`: it proves nothing about error growth. A linear
   *upper* bound is not linear growth. And one-step Dobrushin coefficient `1` does not
   persist: `f = (0, 0, 1)` on `Fin 3` has `delta(Q) = 1` but `f^[2]` constant, so
   `delta(Q^2) = 0` (`Regression.collapse_dobrushin_two_zero`).
2. **"Decoders are right or wrong, never in between."** Withdrawn as stated. True for a
   deterministic decoder on a point-mass input; a randomized decoder has fractional error
   on a deterministic trajectory, and TV error transfer applies to it unchanged.
3. **"The window shrinks by exactly one cell per step; same-window descent only for
   `b = 0`."** Withdrawn. `tmBlock_descends_shrink` is a *uniform sufficiency* statement
   (radius `r` determines radius `r - b`); it is not necessary for a given machine (the
   identity machine keeps any window), and worst-case sharpness (a pure shift needs radius
   `s + b`) is a separate, unformalized necessity theorem.
4. **"This is Mathlib's `TM0` semantics written out."** Withdrawn. `tmStep` is a total,
   simultaneous write-and-move model; `TM0` is partial and moves *or* writes. The window
   theorem holds for the custom model; a `TM0` adapter (simulation, halting, step-count
   overhead) is a separate target.

Two further facts from the review, both now theorems:

- **Block descent does not exclude intermediate leakage.** `f (a, b) = (b, a)` has
  `f^[2] = id`, which descends onto the first coordinate while `f` does not
  (`Regression.swap_block_descends_not_step`); and `Q[f^[2]] != Q[f]^2`
  (`Regression.swap_Q_sq_ne_Q_block`). A block theorem must not equate these kernels.
- **The deterministic defect gap [KERNEL, `machineDefect_gap`].** For a deterministic
  machine with positive weights on a finite nonempty configuration space,

      `c = 0  or  1 <= c < 2`.

  Each commutator row has `L^1` mass `2 (1 - Q(q x, q (f x)))` (`detKernel_row_residual_l1`);
  positivity gives `< 2`; failure of descent puts two outputs in one fiber, one with mass
  `<= 1/2`, giving `>= 1`. Consequence (`machineDefect_linear_budget_vacuous`): in every
  nonexact deterministic case the linear budget is `>= 1/2` at `h = 1` and exactly `1`
  for `h >= 2`, so the uniform additive certificate **cannot certify any target
  `p < 1/2` at any positive horizon**. This is a limitation of the linear certificate,
  not a lower bound on actual error: the reader machine has `c = 1` but `delta(Q) = 0`,
  and the contraction-aware budget `(c/2) sum delta^j = 1/2` is sharp there
  (`Regression.reader_coarse_row`); the collapse example has positive defect with
  actual error decaying as `2^{-h}`.

The reviewer's deduction was made from our definitions in prose; the formalization is
ours. It is, in our judgment, the most useful result of the evening, because it says
exactly which certificate is worth having for machines: not the linear one.

Neither item above is a slogan.

## 5b. Second correction round: exact error, all-or-nothing, and terminal vs path **[KERNEL + CORRECTED]**

Added after the gap, then corrected by a second follow-up review the same evening.

- **Exact terminal error** (`machine_point_tv_exact`): from a point input,
  `tv = 1 - Q^h (q x) (q (f^[h] x))` - an equality. `machine_mixture_tv_le`: for general
  input laws this is only an upper bound (mixture discrepancies cancel: uniform input to the
  uniform reader has terminal TV `0` while the average point error is `1/2`).
- **All-or-nothing** (`descends_iff_defect_lt_one`, `linear_certificate_implies_descends`):
  `Descends f P <-> c < 1`; the uniform additive certificate certifies any `p < 1/2` only
  for exact factor maps. Correction: the defect is **gapped, not quantized** - nonzero
  values fill `[1, 2)` continuously (weights `p, 1-p` on the reader give `c = 2 max(p, 1-p)`).
- **Constant-row regime** (`dobrushin_zero_iff_rows_equal`, `machine_error_of_dobrushin_zero`):
  with `delta(Q) = 0` the terminal error from a point is `1 - rho (q (f^[h] x))` for a fixed
  row `rho` - uniformly bounded and non-accumulating, but not necessarily constant (the
  endpoint moves; non-uniform reader weights oscillate between `p` and `1 - p`). Corrections:
  the reference row is maximally uncertain, not "confidently wrong"; `delta(Q) = 0` says
  nothing about whether the fine machine preserves its input (`f = (1,3,0,3)` on `Fin 4`
  has the same `Q` and erases everything in three steps).
- **Sharpness** (`Regression.reader_budget_sharp`): on the uniform reader the exact terminal
  error equals the contraction-aware budget `1/2` at every positive horizon, from every
  point input; the linear budget is `1` from two steps.
- **Terminal is not path** (`machine_path_tv_exact`, `Regression.reader_path_tv`): the TV
  between the actual coarse *trajectory* and the reference Markov path law is
  `1 - prod_{j<h} Q (z_j) (z_{j+1})`; on the uniform reader this is `1 - 2^{-h}` while the
  terminal error is `1/2`. **A bounded terminal discrepancy coexists with a trajectory
  discrepancy tending to one.** Neither is the probability that an actual decoder execution
  fails; that needs the decoder and the labels.

The three obligations, restated more strictly after this round: *semantics* = input
classes, intended answers, and the decoder's decision rule (not endpoint identification);
*approximation* = actual/reference discrepancy for the declared input law and the declared
observable (terminal or path); *physics* = a proved realization and, for any obstruction,
a complete-state contraction. Mixing of `Q` discharges none of them.

## 6. Ledger

| Module (today) | Declarations | Closure | Audit |
|---|---|---|---|
| `StatisticalHorizon` | 14 | standard | 0 fail |
| `DeterministicKernels` | 5 | standard | 0 fail |
| `TerminalDecoding` | 115 | standard | 0 fail |
| `BlockRenormalization` | 10 | standard | 0 fail |
| `DeterministicLumpability` (+ `Regression`) | 19 | standard | 0 fail |
| `MachineCertificate` (+ `Gap`, `Exact`, `Path`, `Regression`) | 51 | standard | 0 fail |

Branches: see the commit log (`MachineCertificate` and its corrections landed after v0.1). Receipts under
`docs/receipts/`. Two lean-triage false positives found and fixed today (hypotheses the
statement depends on; compiler-generated lemmas), selftest passing.

## 7. One paragraph for the record

Yesterday the computation axis of SGC was an analogy that a reviewer correctly took
away. Today it is a table of iffs on Mathlib's machine model: exact coarse-graining of a
deterministic computation is a factor map, the renormalized machine is a machine, block
codes are kernel powers, halting is preserved by the block tower, and a coarse
description that forgets what the control flow reads has positive defect. The
quantitative SGC theory is the deformation of that exact sector. This does not make a
fluid compute, and it does not touch regularity. It makes the sentence "this flow
computes" *mean something in SGC* - the existence of a factor map - and it makes the
sentence "this coarse-graining of a computer loses information" a computable, positive
number. That is the right foundation for the part of the program that was, until this
morning, the least defensible.
