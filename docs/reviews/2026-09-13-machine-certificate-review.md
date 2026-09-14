# MachineCertificate review: proved bridges, claim corrections, and the deterministic defect gap

## Assessment and audit scope

The new module supplies a useful formal interface between finite deterministic dynamics, exact factor maps, and terminal decoding guarantees, alongside a separate finite-propagation theorem for a head-relative tape model. Its inspected theorem statements are mathematically sound; the main issues are stronger interpretations in the docstrings and project narrative, not an identified false theorem. In particular, the statements do not establish necessary tape-window shrinkage, positive linear error growth, or a fully composed certificate from Mathlib’s TM0 semantics to a finite observed machine. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean))

A further consequence derived below is especially relevant to the program: with the canonical positively weighted coarse kernel and maximum-row \(L^1\) norm, deterministic dynamics has a defect gap:

\[
\boxed{c=0\quad\text{or}\quad 1\le c<2.}
\]

This is an elementary mathematical deduction from the inspected definitions, independently reviewed here, not a newly compiled Lean declaration or a claim of literature novelty. It means that this particular uniform linear certificate has no small-positive-defect regime within deterministic dynamics and hard partitions.

The audit used the source at `1335f3a3d2c36a2516b8213b634c57edca5cba31`, its dependencies, the committed receipt, and the pinned Mathlib definitions. No Lean source was edited, no repository changes were pushed, and no independent Lean build was run.

## What the declarations establish

| Component | Supported statement | Important boundary |
|---|---|---|
| Terminal TV transfer | For finite deterministic \(f\), the actual and reference observed laws differ by at most \(\min(1,hc/2)\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean)) | This is an upper bound, not an error-growth law. |
| Exact descent | `Descends f P` makes the canonical quotient deterministic and the observed/reference TV exactly zero at every finite horizon. ([DeterministicLumpability](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/DeterministicLumpability.lean)) | Exact prediction does not prove that the observation retains the answer. |
| Reliability | Reference conditional-error bounds transfer separately for each class when the stated additive budget fits. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean)) | Reference correctness remains a hypothesis. |
| Point-law theorem | A point-mass input remains a point mass after deterministic evolution and partition observation. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean)) | Only a deterministic decoder on that point observation has error restricted to zero or one. |
| Dobrushin theorem | A deterministic kernel with two distinct outputs has one-step coefficient \(1\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean)) | Its later powers can become constant; an inexact coarse kernel need not be deterministic. |
| Product-coordinate criterion | Descent under projection onto the first coordinate is equivalent to independence of the next first coordinate from the forgotten coordinate. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean)) | `descends_fst_iff` is a definitional equivalence, proved by `Iff.rfl`. |
| Window propagation | With moves bounded by one and \(r\ge b\), agreement on radius \(r\) implies agreement on radius \(r-b\) after \(b\) steps, including the control state. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean)) | Uniform sufficiency, not a necessity theorem for each machine. |

None of the machine-certificate hypotheses requires stationarity or normalization of the positive reference weights. The decoder type inherited from `TerminalDecoding` permits a probability of outputting one anywhere in \([0,1]\), so the “never in between” sentence must explicitly restrict both the initialization and the decoder. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean), [TerminalDecoding](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/TerminalDecoding.lean))

## The deterministic defect gap

### Exact row formula

Assume a nonempty finite state space \(V\), quotient map \(q:V\to Y\), deterministic update \(f\), and weights \(\pi(x)>0\). The canonical coarse row is the conditional weighted distribution of \(q(f(x))\) within each input fiber; this is the formula used by `coarseGenerator_detKernel_eq`. ([DeterministicLumpability](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/DeterministicLumpability.lean))

Writing

\[
w_A=\sum_{q(x)=A}\pi(x),
\qquad
Q(A,B)=\frac{\sum_{q(x)=A,\ q(f(x))=B}\pi(x)}{w_A},
\]

the row of \(T_fJ\) at \(x\) is the point mass at \(B_x=q(f(x))\), whereas the row of \(JQ\) is \(Q(q(x),\cdot)\). Consequently,

\[
\begin{aligned}
\sum_B\left|\mathbf1[B=B_x]-Q(q(x),B)\right|
&=1-Q(q(x),B_x)+\sum_{B\ne B_x}Q(q(x),B)\\
&=2\bigl(1-Q(q(x),B_x)\bigr).
\end{aligned}
\]

Thus the defect defined by `machineDefect` satisfies

\[
c=2\left(1-\min_{x\in V}Q(q(x),q(f(x)))\right).
\]

The proof uses probability-row normalization of \(Q\), not stationarity of \(\pi\). Quotient labels are occupied fibers by construction, so their denominators are positive.

### Gap proof

If \(f\) descends, each coarse row is the appropriate point mass and \(c=0\). The converse is already supplied by the zero-commutator equivalence. ([DeterministicLumpability](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/DeterministicLumpability.lean))

If \(f\) does not descend, some input fiber reaches at least two different output fibers. Their positive probabilities sum to one, so one attained output has probability at most \(1/2\). Choose a fine state reaching that output. Its row residual is at least \(2(1-1/2)=1\), giving \(c\ge1\).

For every fine state,

\[
Q(q(x),q(f(x)))\ge\frac{\pi(x)}{w_{q(x)}}>0.
\]

Finiteness makes the minimum of these positive numbers positive, hence \(c<2\). This proves the displayed dichotomy; the empty-state case can be handled separately using the library’s empty-matrix norm convention.

More generally, a fiber with \(k\) distinct output labels gives

\[
c\ge2\left(1-\frac1k\right).
\]

The gap is about the maximum-row norm, not a quantitative lower bound on the differently defined weighted `defectSq`. The existing `defect_pos_of_leak` proves positivity of the latter, and should not be silently substituted for this new quantitative statement. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean))

### Consequence for the stated horizon

For every nonexact deterministic partition, the linear budget is therefore

\[
\min(1,hc/2)=
\begin{cases}
0,&h=0,\\
c/2\in[1/2,1),&h=1,\\
1,&h\ge2.
\end{cases}
\]

Accordingly, the sufficient condition in `machine_terminal_reliability`, namely \(\beta_b+\min(1,hc/2)\le p_b\) with \(\beta_b\ge0\), cannot certify an individual target \(p_b<1/2\) at any positive horizon in a nonexact case. This is a consequence of the theorem’s actual additive hypothesis. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean))

**This limits the certificate, not the machine.** Actual errors may remain small or vanish, and law-specific or decoder-specific estimates can be sharper. The separately available exact terminal-matrix budget may also improve on the linear estimate; no monotone actual error growth follows from the gap. ([TerminalDecoding](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/TerminalDecoding.lean))

At one step, however, the gap is not merely slack introduced by telescoping: some fine input point really has actual/reference TV at least \(1/2\). The chosen norm protects every fine input, including rare or semantically irrelevant states; the required input classes need not contain the maximizing point.

## What the Dobrushin result does and does not say

### The exact-descent assumption matters

The two-point characterization

\[
\delta(K)=\max_{x,x'}\operatorname{TV}(K(x,\cdot),K(x',\cdot))
\]

is the standard Dobrushin contraction coefficient. Distinct deterministic outputs give distinct point masses, immediately yielding coefficient one. ([Polyanskiy and Wu, slide 7](https://people.lids.mit.edu/yp/homepage/data/ita2015-pres.pdf))

However, `mixing_budget_trivial_of_quotient_machine` assumes `Descends f P`, which already forces \(c=0\). Its conclusion is only \(\delta(Q)=1\), not an error lower bound or a theorem asserting linear accumulation. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean))

The finite geometric sum becomes \(h\) when \(\delta(Q)=1\), but its multiplier is zero in this exact-descent application. The infinite-horizon formula \(c/[2(1-\delta)]\) cannot be applied at \(\delta=1\): its formal theorem explicitly requires \(\delta<1\). ([TerminalDecoding](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/TerminalDecoding.lean))

Thus “the geometric estimate reduces to the linear expression” is algebraically correct for the finite sum. “This proves that computational error grows linearly” is not.

### One-step coefficient one does not imply persistent nonmixing

Consider the following explicit deterministic example:

\[
f(0)=0,\qquad f(1)=0,\qquad f(2)=1.
\]

With the identity observation, \(c=0\) and \(\delta(T_f)=1\), but \(f^2\) is constant, so \(\delta(T_f^2)=0\). All initial laws coalesce after two steps. This counterexample satisfies the positive-reference-weight assumptions; adding positive stationary weights would be a materially stronger assumption.

The appropriate all-horizons statement is conditional: \(\delta(T_f^h)=1\) whenever \(f^h\) has two distinct outputs. A permutation on at least two states satisfies this at every horizon. Neither property characterizes computation.

### Inexact coarse kernels of deterministic machines can mix

The existing regression machine is \(f(a,b)=(b,b)\), observed only through \(a\). ([DeterministicLumpability](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/DeterministicLumpability.lean))

With uniform weights, direct calculation gives

\[
Q=\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix},
\qquad c=1,\qquad\delta(Q)=0.
\]

The fine dynamics is deterministic, but its nonexact reference coarse kernel mixes immediately. Its geometric TV budget is \(1/2\) at every positive horizon, genuinely improving on the linear budget of \(1\) from step two onward. It still cannot certify an error target below \(1/2\) through the uniform additive reliability condition.

Indeed, every positive-horizon geometric-sum budget includes its initial \(c/2\) term, so the defect gap also prevents that uniform refinement from certifying \(p_b<1/2\) through the same additive argument. It does not make the geometric bound itself trivial: \(1/2\) remains a meaningful TV bound.

This example also separates reference mixing from actual information loss. The fine states \((0,0)\) and \((1,1)\) are fixed points with permanently distinct observed outputs, even though their reference laws become identical after one step. Contraction of \(Q\) cannot substitute for the independently required complete-state contraction.

A second direct calculation illustrates decreasing actual approximation error. Use \(f(0)=0,f(1)=0,f(2)=1\), uniform weights, and fibers \(A=\{1,2\}\), \(B=\{0\}\). Then

\[
Q=\begin{pmatrix}1/2&1/2\\0&1\end{pmatrix},\qquad c=1.
\]

Starting at state \(2\), actual/reference observed TV is \(1/2\) at step one and \(2^{-h}\) for \(h\ge2\). The actual error decreases even while the linear certificate is trivial.

## Window sufficiency, sharpness, and blocking

### What the window theorem proves

The exact statement includes the hypothesis \(r\ge b\), and its conclusion concerns two different observation relations:

\[
c\sim_r c'
\quad\Longrightarrow\quad
f^b(c)\sim_{r-b}f^b(c').
\]

It is a finite-domain-of-dependence guarantee, not an endomorphism of one fixed-radius quotient. The source’s one-step docstring correctly says “at most one,” while the module header and final theorem docstring overstate this as “exactly” and “same window only for \(b=0\).” ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean))

An immediate counterexample to necessity is

\[
\operatorname{nxt}(q,a)=q,\qquad w(q,a)=a,\qquad \operatorname{mv}(q,a)=0.
\]

This makes `tmStep` the identity. Every tape window descends to itself at every horizon.

The corrected interpretation is: an input radius \(s+b\) suffices to determine the output radius \(s\) after \(b\) steps for every machine satisfying the move bound. In symmetric-window coordinates, that is \(b\) extra cells of radius, or \(2b\) extra tape cells in total, not a universal requirement of exactly \(b\) extra stored cells.

### A separate sharpness theorem is available

Take a pure right-moving machine, with unchanged writes and constant control. Its head-relative tape satisfies

\[
t_b(j)=t_0(j+b).
\]

For a required output window \([-s,s]\), the initial coordinate \(s+b\) must be recoverable. With at least two symbols, two tapes can agree on every smaller centered window but differ at \(s+b\), producing different outputs at coordinate \(s\).

This supplies a worst-case sharpness witness for centered-window representations. It is not present as a necessity theorem in the inspected module, and it would not establish an unrestricted computational-space lower bound: an asymmetric observation tailored to a known pure shift is a different representation.

### Endpoint descent permits intermediate leakage

For \(f(a,b)=(b,a)\) and observation \(q(a,b)=a\),

\[
q(f(a,b))=b,\qquad q(f^2(a,b))=a.
\]

Thus the one-step map leaks, but the two-step block descends exactly. The phrase “no information enters during the block” is stronger than endpoint independence and is not equivalent to block descent.

There is also a coarse-kernel distinction. With uniform weights, \(Q[f]\) has both rows \((1/2,1/2)\), whereas \(Q[f^2]=I\), so

\[
Q[f^2]\ne Q[f]^2.
\]

The source correctly proves commutation of blocking and quotienting under one-step descent. Outside that regime, `blocked_terminalError_eq` retains the coarse kernel constructed from \(f^b\); it does not identify it with the \(b\)-th power of the original coarse kernel. ([DeterministicLumpability](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/DeterministicLumpability.lean), [BlockRenormalization](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/BlockRenormalization.lean))

## The remaining semantic interfaces

The components do not yet form a single instantiated end-to-end theorem. The finite certificate assumes `[Fintype V]`, while the new tape theorem acts on \(Q\times(\mathbb Z\to\Gamma)\); the latter is used only through window relations. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean))

There is also a concrete distinction between step semantics. The custom `tmStep` is total and can write and move simultaneously, whereas the pinned Mathlib TM0 transition returns an `Option` and executes either a move or a write. No explicit translation or simulation theorem connecting those definitions is supplied by the new module. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean), [Mathlib TM0](https://github.com/leanprover-community/mathlib4/blob/c98ae54af00eaefe79c51b2b278361ca94e59bfb/Mathlib/Computability/PostTuringMachine.lean))

These differences need not be fundamental obstacles. They identify specific next proof obligations:

- **Semantic adapter:** Relate the head-relative model to TM0 configurations and transitions, declaring any step-count conversion and treatment of halting.
- **Finite realization:** Define a finite configuration model with boundary behavior, retained controller state, and a proved horizon over which it agrees with the infinite machine.
- **Observation alignment:** Alternatively, construct the changing-radius finite quotient maps directly and prove their composition law, rather than assuming one fixed coarse kernel.
- **Answer semantics:** Exhibit the relevant input classes and terminal decoder, and prove the reference correctness hypotheses.
- **Physical instantiation:** Only afterward supply any proposed physical realization and complete-state contraction, including retained records, redundancy, and correction resources.

The generic halting-faithful block theorem remains valid and useful: it relates partial-step blocking to `Turing.eval`. It does not, by itself, supply the missing translation to the new total head-relative step or a finite terminal decoder. ([BlockRenormalization](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/BlockRenormalization.lean))

## Verification evidence and recommended next work

The committed receipt records the 15 manually named theorem/lemma targets with closures contained in `propext`, `Classical.choice`, and `Quot.sound`; several use no axioms. That supports the reported trusted-base scope of the audited environment, not the stronger informal interpretations. ([Audit receipt](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/docs/receipts/machine-certificate/receipt.json))

The same receipt reports a dirty working tree at an earlier base commit, `evidence.build.skipped = true`, and kernel replay skipped because the build was not verified. Its summary check nevertheless labels the build check “pass”; the explicit execution evidence should govern the interpretation, and this receipt should not be cited as an independently reproduced clean build of either final commit. ([Audit receipt](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/docs/receipts/machine-certificate/receipt.json))

The two reported commits contain the same `MachineCertificate.lean` Git blob, `deb527e77496407b8d004e6556d52311d8143bfb`, as checked through authenticated GitHub retrieval. The reported 3315/3146 build-job totals were not independently reproduced. Numerical sanity checks confirmed the row formula and defect gap in 1,536 finite examples, alongside the explicit counterexamples above; the general gap claim rests on its proof, not on these checks.

Recommended order:

- **Correct the prose:** Replace necessary shrinkage with uniform sufficiency; qualify the decoder claim; separate one-step noncontraction from persistent nonmixing; remove the inference to actual linear error growth.
- **Formalize the gap:** Prove the deterministic residual-row formula and `non_descends → 1 ≤ machineDefect`. Register saturation of the linear budget at horizons at least two as a corollary.
- **Add regressions:** Identity-window preservation, a deterministic map with constant square, the mixing coarse kernel of `reader`, and swap-induced recovery of two-step descent.
- **Close the semantic interfaces:** Connect TM0, the head-relative step, and a finite horizon-correct observation model before calling the chain an instantiated machine certificate.
- **Choose the quantitative regime deliberately:** Use reachable-law or decoder-specific estimates when appropriate; use stochastic kernels or different observation models only with explicit semantic accounting. Do not merely change the norm to obtain a favorable number.

The accomplishment is a cleaner, reusable formal framework separating temporal blocking, observational closure, and answer reliability. Its most useful immediate implication may be that the present worst-row metric exposes a sharp limitation of approximate deterministic quotienting, rather than providing a long-horizon small-error theory. None of the inspected results establishes a space-complexity lower bound, a physical integration-cost law, or a Navier–Stokes obstruction. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/MachineCertificate.lean), [BlockRenormalization](https://github.com/JasonShroyer/sgc-lean/blob/1335f3a3d2c36a2516b8213b634c57edca5cba31/src/SGC/Bridge/BlockRenormalization.lean))
