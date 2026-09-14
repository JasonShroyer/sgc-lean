# MachineCertificate follow-up: sharp terminal error versus trajectory fidelity

## Verdict and verified scope

The new source implements the deterministic defect gap, the exact point-input terminal formula, the constant-row characterization of zero Dobrushin coefficient, and the reader sharpness theorem with the stated positive-horizon quantifiers. The inspected proofs support those statements; they substantially improve the earlier narrative by replacing a loose linear upper bound with an attained contraction-aware bound on a specific deterministic example. ([MachineCertificate at ad37a88](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

The precise accomplishment is a **sharp terminal-law approximation theorem**, not a proof of trajectory fidelity, preservation of all input information, or successful answer decoding. The defect is separated from zero by a gap in the specified norm; its nonzero values are not restricted to a discrete set.

| New result | Exact scope |
|---|---|
| `machineDefect_gap` | For nonempty finite state space, deterministic update, hard partition, and strictly positive reference weights: \(c=0\) or \(1\le c<2\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean)) |
| `machine_point_tv_exact` | At every horizon \(h\), including zero, point-input terminal TV is \(1-Q^h(qx,q(f^h x))\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean)) |
| `dobrushin_zero_iff_rows_equal` | Zero coefficient is equivalent to identical rows; the theorem itself does not require stochasticity. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean)) |
| `pow_row_const_of_rows_equal` | With stochasticity and identical rows, every positive matrix power has the same rows. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean)) |
| `machine_error_of_dobrushin_zero` | For point input \(x\), common coarse row \(\rho\), and \(h\ge1\), terminal TV is \(1-\rho(q(f^h x))\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean)) |
| `reader_budget_sharp` | For the fixed reader map \(f(a,b)=(b,b)\), observation \(q(a,b)=a\), and uniform reference weights, every point input and every positive horizon attain mixing budget \(1/2\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean)) |

The coefficient convention agrees with the standard two-point TV characterization, including the factor \(1/2\) in total variation. No stationarity assumption on the reference weights is needed for these conclusions. ([Polyanskiy and Wu, slide 7](https://people.lids.mit.edu/yp/homepage/data/ita2015-pres.pdf), [MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

## The companion path-law calculation

The exact terminal formula concerns a single coordinate of a trajectory. Its formal statement contains the endpoint \(q(f^h x)\), not a probability distribution on complete observed paths. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

For a point input, define the actual observed path

\[
z_j=q(f^j x),\qquad 0\le j\le h.
\]

Now define a reference Markov path that starts at the same \(z_0=qx\) and uses transition matrix \(Q\) at every step. The actual path law is the point mass at \((z_0,\ldots,z_h)\), and the reference assigns that path probability

\[
\prod_{j=0}^{h-1}Q(z_j,z_{j+1}).
\]

Applying the point-mass TV identity on the finite path space gives the following additional mathematical deduction:

\[
\boxed{
\operatorname{TV}(\text{actual path law},\text{reference path law})
=1-\prod_{j=0}^{h-1}Q(z_j,z_{j+1}).
}
\]

This calculation is not a declaration in the inspected module. Its proof is the same elementary identity used by `tv_point_prob`, applied to a different sample space. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

For the uniform reader, every transition probability of \(Q\) is \(1/2\). Therefore:

\[
\begin{aligned}
\operatorname{TV}(\text{terminal laws})&=\frac12 &&(h\ge1),\\
\operatorname{TV}(\text{whole-path laws})&=1-2^{-h} &&(h\ge0).
\end{aligned}
\]

The terminal equality is the new formal sharpness result; the whole-path equality is derived here from the proved reader kernel entries. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

| Horizon | Terminal TV | Whole-path TV |
|---|---:|---:|
| 1 | \(1/2\) | \(1/2\) |
| 2 | \(1/2\) | \(3/4\) |
| 3 | \(1/2\) | \(7/8\) |
| \(h\to\infty\) | \(1/2\) | Approaches \(1\) |

Thus “non-accumulating” is defensible for this reader’s terminal error, but not for fidelity of the reference’s entire generated trajectory. Neither quantity is automatically the probability that an actual machine execution or its decoder fails.

## A defect gap, not discrete quantization

For the same reader, replace uniform reference weights by

\[
\pi(a,0)=p,\qquad \pi(a,1)=1-p,\qquad 0<p<1.
\]

Direct calculation gives identical coarse rows \((p,1-p)\), zero Dobrushin coefficient, and

\[
c=2\max\{p,1-p\}.
\]

As \(p\) ranges from \(1/2\) toward \(1\), the defect varies continuously over \([1,2)\). This example uses exactly the canonical conditional averaging and residual-row formula in the source. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

The safe headline is:

> For finite deterministic dynamics with hard partition observations and canonical positive reference weights, the maximum-row closure defect has an exactness gap: any defect below one is zero.

This does not prohibit small law-specific prediction errors, small decoder-error differences, or small errors under other metrics and observation models. It also does not automatically transfer a finite-state norm theorem to arbitrary continuous-state flow encodings.

There is a second surviving limitation of the uniform certificate. Every positive-horizon geometric-sum budget contains the initial \(c/2\) term:

\[
B_h^{\mathrm{mix}}
=\min\left\{1,\frac c2\sum_{j=0}^{h-1}\delta(Q)^j\right\}
\ge\frac12
\]

whenever the deterministic quotient is nonexact. Consequently, even the contraction-aware uniform additive argument cannot certify a target below \(1/2\) in that regime. The reader’s \(1/2\) bound is meaningful and sharp, but sharpness does not turn it into a high-reliability guarantee. ([TerminalDecoding](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/TerminalDecoding.lean), [MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

## What zero reference contraction does not imply

### It does not mean the fine machine preserves its input

The reader itself forgets the first input coordinate: \((0,b)\) and \((1,b)\) both become \((b,b)\). It preserves \(b\), not the entire initial configuration.

A stronger counterexample uses states \(0,1,2,3\), fibers \(A=\{0,1\}\), \(B=\{2,3\}\), uniform weights, and

\[
f(0)=1,\quad f(1)=3,\quad f(2)=0,\quad f(3)=3.
\]

Both coarse rows are \((1/2,1/2)\), so \(\delta(Q)=0\) and \(c=1\), yet \(f^3(x)=3\) for every input. The fine dynamics completely erases its input after three steps while the point-input terminal approximation error remains exactly \(1/2\).

The identity of the coarse rows constrains the reference channel, not injectivity or information preservation of \(f\). A theorem about “never forgetting” requires separate assumptions.

### It does not make exact terminal error constant in time

The common reference row is constant, but its argument \(q(f^h x)\) can change. The theorem therefore permits temporal variation in \(1-\rho(q(f^h x))\). ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

For example, use the four-cycle \(0\to1\to2\to3\to0\), the same fibers, and weights

\[
\pi=(p,1-p,1-p,p).
\]

Both coarse rows equal \((p,1-p)\). Starting at \(0\), the positive-horizon errors repeat

\[
1-p,\quad p,\quad p,\quad 1-p,\quad\ldots
\]

For \(p=4/5\), this is \(1/5,4/5,4/5,1/5,\ldots\). The bound is uniform in time, but the actual error can increase, decrease, and oscillate.

### It does not establish confident misprediction

The sharp reader example predicts the uniform distribution on two outputs. That forecast is maximally uncertain, rather than confident in a wrong output.

“Constant-row reference regime” or “instantaneously mixing reference” accurately names the mathematics. Furthermore, “the coarse variable carries no information about its successor” must be qualified as a statement about the reference channel: the reader’s actual observations equal the retained bit \(b\) at all times after step one, and hence retain perfect successive-time dependence when \(b\) varies.

## Point inputs, class laws, and answer semantics

The exact formula is indexed by `pointMass x`. A general input distribution can have smaller actual/reference TV than the average of its point-input errors, because differences can cancel when laws are mixed. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

In particular, a uniform input over all four reader configurations gives identical actual and reference terminal laws at every positive horizon, hence TV zero. Every constituent point input still has TV \(1/2\).

For a probability law \(\mu\), convexity instead gives the valid bound

\[
\operatorname{TV}(\mu T_f^hJ,\mu JQ^h)
\le
\sum_x\mu(x)\left[1-Q^h(qx,q(f^h x))\right].
\]

This is a derived upper bound, not a replacement equality. Apply it separately to each conditional input law when transferring class-specific decoder errors.

The three obligations should remain:

- **Semantics:** Specify the task, input classes, target answers, and common decoder; prove the required reference correctness or corresponding semantic alignment. Naming the endpoint alone does not prove its decoded answer is correct.
- **Approximation:** Bound actual/reference observed-law discrepancy for the relevant inputs and horizon. The exact endpoint formula handles point inputs; path-law fidelity is a distinct object.
- **Physical realization and contraction:** Establish the intended realization and any independently required complete-state contraction, accounting for retained history, controllers, and correction resources. Merely introducing observation noise does not discharge this obligation.

The source retains `hRef` as a decoder-correctness hypothesis and `hContract` as an explicit full-state contraction hypothesis. Zero Dobrushin coefficient of the reference \(Q\) is not a substitute for either. ([TerminalDecoding](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/TerminalDecoding.lean))

Finally, “computable” should be read conditionally: the equality is a finite expression, numerically evaluable for effective finite tables and suitable effective weights, such as rational weights. The formal statement quantifies over arbitrary real weights in a `noncomputable section`; it does not itself provide an executable evaluator, an efficient algorithm, or a way to obtain the endpoint without determining the machine’s evolution. ([MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean))

## Audit status and next formal target

Authenticated retrieval found identical source blobs at the two reported commits. The new receipt records target axiom closures limited to `propext`, `Classical.choice`, and `Quot.sound`, while again recording a dirty working tree, a skipped build, and skipped kernel replay; no independent Lean rebuild was performed in this review. ([Mirrored MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/6b43aa8/src/SGC/Bridge/MachineCertificate.lean), [MachineCertificate](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/src/SGC/Bridge/MachineCertificate.lean), [Audit receipt](https://github.com/JasonShroyer/sgc-lean/blob/ad37a88/docs/receipts/machine-certificate/receipt.json))

The natural complementary target is the finite observed-path identity

\[
\operatorname{TV}(\delta_{(z_0,\ldots,z_h)},\mathsf{PathLaw}_{Q,qx})
=1-\prod_{j<h}Q(z_j,z_{j+1}),
\]

followed by the reader regression \(1-2^{-h}\). Together with the existing terminal equality, this would formalize exactly how a sharp bounded terminal discrepancy can coexist with path-law discrepancy approaching one, without making any claim about actual computational failure.
