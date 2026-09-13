# Finite-state terminal decoding certificate

## Scope and status

This is a mathematical theorem specification for a finite-state certificate built on `SGC.Renormalization.KernelHorizon`. The audited source is `JasonShroyer/sgc-lean`, branch `opus/two-horizons`, commit `c8dee8cd7c899d105386f7981c76b896a985b7af`; the existing theorem uses a stochastic fine kernel, a partition, strictly positive reference weights, and the maximum-row \(L^1\) matrix norm. ([Pinned KernelHorizon source](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

The statements below concern one terminal answer at a specified step \(m\). They make no fluid assumptions, no claim of computational universality, and no automatic guarantee about an entire execution.

Status labels distinguish three kinds of statements:

- **Existing:** A declaration inspected in the pinned repository.
- **Standard consequence, proposed:** A finite-probability or matrix consequence with a proof outline below; not claimed to have been implemented or kernel-checked.
- **External obligation:** A semantic, modeling, or contraction hypothesis that this certificate does not prove.

“External” means independently supplied to this theorem package, not necessarily an open research problem. A fully specified finite example may discharge these obligations by direct computation.

No Lean files were edited, and no independent Lean build was performed. Proposed theorem identifiers below are specification names, not claims that those declarations already exist.

## Exact data and conventions

### Existing kernel interface

Fix the following data:

| Symbol | Type or hypothesis | Repository correspondence |
|---|---|---|
| \(V\) | Finite microscopic state type, with decidable equality | `{V : Type*} [Fintype V] [DecidableEq V]` |
| \(P\) | Partition of \(V\) | `P : Partition V` |
| \(Y\) | Coarse state type | `P.Quot` |
| \(q:V\to Y\) | Partition map | `P.quot_map` |
| \(T\) | Matrix \(V\times V\to\mathbb R\) | `T : Matrix V V ℝ` |
| \(h_T\) | \(T(x,x')\ge0\), \(\sum_{x'}T(x,x')=1\) | `KernelHorizon.IsStochastic T` |
| \(\pi\) | Reference weights \(V\to\mathbb R\) | `pi_dist` |
| \(h_\pi\) | \(\pi(x)>0\) for every \(x\) | `∀ x, 0 < pi_dist x` |
| \(J\) | Matrix \(V\times Y\), \(J(x,y)=\mathbf1_{\{q(x)=y\}}\) | `lift_matrix P` |
| \(Q\) | Canonical coarse matrix \(Y\times Y\) | `CoarseGenerator T P pi_dist` |

These are the hypotheses and objects appearing in the existing stochasticity and closure-error theorems; neither normalization nor stationarity of \(\pi\) is required. Despite the historical name `CoarseGenerator`, \(Q\) here is a discrete-time stochastic kernel, not a continuous-time generator. ([KernelHorizon declarations](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

In ordinary mathematical notation, its entries are

\[
Q(y,z)=
\frac{\displaystyle
\sum_{x:q(x)=y}\pi(x)
\sum_{x':q(x')=z}T(x,x')}
{\displaystyle\sum_{x:q(x)=y}\pi(x)}.
\]

Every quotient block is nonempty, and positivity of \(\pi\) makes its denominator positive. The existing `coarseKernel_isStochastic` establishes the stochasticity of \(Q\) under precisely \(h_T,h_\pi\). ([Existing coarse-kernel result](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

Use row-vector evolution throughout:

\[
(\rho M)(z)=\sum_x\rho(x)M(x,z).
\]

Thus \(J\) pushes a microscopic probability law to a coarse probability law. The same matrix pulls a coarse observable back when acting on column observables; these two interpretations must not reverse the matrix order.

### Probability laws and total variation

For a finite type \(X\), define

\[
\operatorname{Prob}(X)
=\left\{\rho:X\to\mathbb R:
\rho(x)\ge0,\ \sum_x\rho(x)=1\right\}.
\]

For \(\rho,\sigma\in\operatorname{Prob}(X)\), use

\[
\operatorname{TV}_X(\rho,\sigma)
=\frac12\sum_{x\in X}|\rho(x)-\sigma(x)|
=\max_{A\subseteq X}|\rho(A)-\sigma(A)|.
\]

This is the probability-distance convention in which \(0\le\operatorname{TV}\le1\), not the unhalved variation norm of a signed measure. The half-\(L^1\) and event-supremum conventions agree with standard statistical testing references. ([Stanford statistical testing notes](https://web.stanford.edu/class/stats311/OldSyllabi/full_notes.pdf))

The new probability laws below, unlike \(\pi\), must be normalized. Their existence entails that the relevant state space is nonempty; an additional nonemptiness hypothesis on the original kernel theorem is unnecessary.

### Norm and error budget

For a matrix \(M:X\times Z\to\mathbb R\), write

\[
\|M\|_{\mathrm{row}}
=\max_{x\in X}\sum_{z\in Z}|M(x,z)|.
\]

This denotes the same maximum-row \(L^1\), or \(L^\infty\)-operator, norm selected locally by `Matrix.linftyOpNormedAddCommGroup` in `KernelHorizon`. No Euclidean, Frobenius, or entrywise-maximum norm may be substituted. ([Norm convention in KernelHorizon](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

Define

\[
C=TJ-JQ,\qquad c=\|C\|_{\mathrm{row}},
\]
\[
E_m=T^mJ-JQ^m,\qquad
\varepsilon_m=\min\left\{1,\frac{mc}{2}\right\}.
\]

Here \(m\in\mathbb N\), with its natural real coercion in inequalities. The existing `kernel_closure_error_le` gives

\[
\boxed{\|E_m\|_{\mathrm{row}}\le mc.}
\]

No stationarity, reversibility, mixing, or semantic-decoding assumption occurs in this result. ([Existing kernel horizon theorem](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

## Probability lemmas and TV conversion

### `prob_vecMul_row_l1_le`

**Standard consequence, proposed.** For any finite rectangular matrix \(M:X\times Z\to\mathbb R\) and \(\rho\in\operatorname{Prob}(X)\),

\[
\sum_z|(\rho M)(z)|\le\|M\|_{\mathrm{row}}.
\]

Proof:

\[
\sum_z\left|\sum_x\rho(x)M(x,z)\right|
\le\sum_x\rho(x)\sum_z|M(x,z)|
\le\sum_x\rho(x)\|M\|_{\mathrm{row}}
=\|M\|_{\mathrm{row}}.
\]

Only nonnegativity and unit mass of \(\rho\) are needed. The matrix \(M\) may have signed entries.

### `tv_vecMul_le_half_row_l1`

**Standard consequence, proposed.** Let \(A,B:X\times Z\to\mathbb R\) be row-stochastic rectangular matrices and \(\rho\in\operatorname{Prob}(X)\). Then \(\rho A,\rho B\in\operatorname{Prob}(Z)\) and

\[
\boxed{
\operatorname{TV}(\rho A,\rho B)
\le\frac12\|A-B\|_{\mathrm{row}}.
}
\]

Proof: stochasticity gives the probability-law conclusions; substitute \(M=A-B\) into the preceding lemma and multiply by \(1/2\). The factor \(1/2\) comes from the definition of TV, not from stationarity or averaging over the two labels.

### `kernel_horizon_tv`

**Standard consequence, proposed.** Under the existing kernel hypotheses, for every \(\rho\in\operatorname{Prob}(V)\) and \(m\in\mathbb N\),

\[
\boxed{
\operatorname{TV}_Y(\rho T^mJ,\rho JQ^m)
\le\frac12\|E_m\|_{\mathrm{row}}
\le\frac{mc}{2}.
}
\]

In particular,

\[
\operatorname{TV}_Y(\rho T^mJ,\rho JQ^m)\le\varepsilon_m.
\]

Proof: \(T^mJ\) and \(JQ^m\) are stochastic rectangular matrices, by stochasticity of \(T,J,Q\), powers, and composition. Apply `tv_vecMul_le_half_row_l1`, then the existing kernel horizon theorem; cap the resulting TV bound at one.

At \(m=0\), \(E_0=0\), \(\varepsilon_0=0\), and both observed laws equal \(\rho J\). When \(c=0\), exact agreement holds at every finite \(m\), but this says nothing about whether \(\rho J\) or its successors distinguish the required answers.

If the actual terminal error matrix can be bounded more sharply, the uniform budget

\[
\varepsilon_m^*=\frac12\|E_m\|_{\mathrm{row}}
\le\min\{1,mc/2\}
\]

may replace \(\varepsilon_m\) everywhere below. The bound by one follows because each row of \(E_m\) is the difference of two probability vectors; adopting this refinement introduces no mixing or stationarity hypothesis.

## Transfer of individual terminal decoding errors

### Experiment and decoder

Fix two probability laws \(\mu_0,\mu_1\in\operatorname{Prob}(V)\). They describe preparations whose required terminal answers are respectively \(0\) and \(1\); assigning those semantic labels is an external obligation.

At the chosen terminal step \(m\), define

\[
\nu_b=\mu_bT^m\in\operatorname{Prob}(V),\qquad
a_b=\nu_bJ\in\operatorname{Prob}(Y),\qquad
r_b=\mu_bJQ^m\in\operatorname{Prob}(Y).
\]

The laws \(a_b\) are the actual terminal observations and \(r_b\) are the reference coarse predictions. No prior probability over \(b\) is required.

Fix one decoder

\[
d:Y\to\{0,1\}.
\]

It is the same function under both alternatives. It may be chosen for the specified \(m\), but may not depend on the unknown true label or uncounted side information.

Define its individual errors:

\[
e_b^{\mathrm{act}}=a_b\{y:d(y)\ne b\},\qquad
e_b^{\mathrm{ref}}=r_b\{y:d(y)\ne b\}.
\]

These are errors conditional on the respective preparation; neither is an equal-prior average.

### `fixed_decoder_error_transfer`

**Standard consequence, proposed.** For each \(b\in\{0,1\}\), individually,

\[
\boxed{
|e_b^{\mathrm{act}}-e_b^{\mathrm{ref}}|
\le\operatorname{TV}(a_b,r_b)
\le\varepsilon_m.
}
\]

Equivalently,

\[
\max\{0,e_b^{\mathrm{ref}}-\varepsilon_m\}
\le e_b^{\mathrm{act}}
\le\min\{1,e_b^{\mathrm{ref}}+\varepsilon_m\}.
\]

Proof: apply the TV event bound to the fixed error event \(\{d\ne b\}\), followed by `kernel_horizon_tv` with \(\rho=\mu_b\). There is no union over labels and no extra factor of two in either individual error bound.

### `terminal_reliability_of_reference_bounds`

**Standard consequence, proposed, with an external semantic premise.** Let \(\beta_0,\beta_1,p_0,p_1\in[0,1]\). Assume separately

\[
e_b^{\mathrm{ref}}\le\beta_b,\qquad
\beta_b+\varepsilon_m\le p_b
\quad(b=0,1).
\]

Then

\[
\boxed{
e_0^{\mathrm{act}}\le p_0
\quad\text{and}\quad
e_1^{\mathrm{act}}\le p_1.
}
\]

The proof is transitivity of the preceding bounds. The reference decoder's correctness, represented by \(e_b^{\mathrm{ref}}\le\beta_b\), is not supplied by kernel closure.

If the same bound \(\beta\) applies to both reference errors and the target is \(p\), a convenient sufficient horizon test is

\[
\beta+\frac{mc}{2}\le p.
\]

For \(c>0\) and \(p\ge\beta\), every integer \(m\) satisfying \(m\le2(p-\beta)/c\) passes this test. This is a sufficient terminal certificate, not an exact failure time; if the inequality fails, no failure of the actual decoder follows.

### Optional randomized decoder extension

All error-transfer statements remain valid for a fixed randomized decoder, described by \(h:Y\to[0,1]\), where \(h(y)\) is the probability of outputting one. Use losses \(\ell_0=h\), \(\ell_1=1-h\), and \(e_b=\sum_y a_b(y)\ell_b(y)\), or the analogous reference expression.

The needed standard lemma is

\[
\left|\sum_y(a(y)-r(y))f(y)\right|
\le\operatorname{TV}(a,r)
\quad\text{when }0\le f\le1.
\]

Its proof splits \(a-r\) into positive and negative parts, each with total mass \(\operatorname{TV}(a,r)\). Randomness must follow the same decoder law under both labels; a label-dependent random seed would change the experiment.

## Observed distinguishability and necessary reliability

Define

\[
D_{\mathrm{obs}}=\operatorname{TV}_Y(a_0,a_1),
\qquad
D_{\mathrm{ref}}=\operatorname{TV}_Y(r_0,r_1).
\]

### `observed_distinguishability_lower`

**Standard consequence, proposed.**

\[
\boxed{
D_{\mathrm{obs}}\ge
\max\{0,D_{\mathrm{ref}}-2\varepsilon_m\}.
}
\]

In particular, the uncapped kernel-budget form is

\[
D_{\mathrm{obs}}\ge D_{\mathrm{ref}}-mc.
\]

Proof:

\[
D_{\mathrm{ref}}
\le\operatorname{TV}(r_0,a_0)
+D_{\mathrm{obs}}
+\operatorname{TV}(a_1,r_1)
\le D_{\mathrm{obs}}+2\varepsilon_m.
\]

The two approximation terms are why this bound has \(2\varepsilon_m\), whereas each decoder-error transfer has only \(\varepsilon_m\). If independent class-specific approximation bounds \(\varepsilon_0,\varepsilon_1\) are available, replace \(2\varepsilon_m\) by \(\varepsilon_0+\varepsilon_1\).

Here a class-specific bound means \(\operatorname{TV}(a_b,r_b)\le\varepsilon_b\); a bound only on one fixed decoder's error difference does not suffice. An exact class-specific budget is \(\varepsilon_b^*=\tfrac12\sum_y|(\mu_bE_m)(y)|\).

The symmetric triangle-inequality argument also gives the optional two-sided refinement

\[
|D_{\mathrm{obs}}-D_{\mathrm{ref}}|
\le\varepsilon_0+\varepsilon_1.
\]

Only the lower side is needed for the compatibility theorem below. The baseline certificate continues to use \(\varepsilon_0=\varepsilon_1=\varepsilon_m\).

### `tv_lower_of_individual_error_bounds`

**Standard consequence, proposed.** If a common decoder, deterministic or randomized, satisfies \(e_0^{\mathrm{act}}\le p_0\) and \(e_1^{\mathrm{act}}\le p_1\), then

\[
\boxed{
D_{\mathrm{obs}}\ge\max\{0,1-p_0-p_1\}.
}
\]

For a deterministic decoder, let \(A=\{d=0\}\). Then

\[
a_0(A)\ge1-p_0,\qquad a_1(A)\le p_1,
\]

so \(D_{\mathrm{obs}}\ge a_0(A)-a_1(A)\ge1-p_0-p_1\). For a randomized decoder, apply the bounded-test lemma to its probability of outputting zero.

For equal targets \(p_0=p_1=p<1/2\), this gives \(D_{\mathrm{obs}}\ge1-2p\). It is necessary, not sufficient for those two individual bounds; the standard equal-prior testing identity instead concerns the minimum average error \((1-D_{\mathrm{obs}})/2\). ([Binary-testing identity](https://web.stanford.edu/class/stats311/OldSyllabi/full_notes.pdf))

## Compatibility with complete-channel contraction

### Direct complete-state version

Declare explicitly that \(V\) is the complete terminally available state: all controller state, usable redundancy, accessible memory, and any stored observation history relevant to the decoder are included. This declaration is a modeling obligation, not a consequence of finiteness or stochasticity.

Define

\[
D_{\mathrm{in}}=\operatorname{TV}_V(\mu_0,\mu_1),
\qquad
D_{\mathrm{full}}=\operatorname{TV}_V(\mu_0T^m,\mu_1T^m).
\]

Assume an independently proved bound, for the same two preparations and terminal step,

\[
\boxed{
D_{\mathrm{full}}\le\Gamma_mD_{\mathrm{in}},
\qquad 0\le\Gamma_m\le1.
}
\tag{Contraction}
\]

Write \(U_m=\Gamma_mD_{\mathrm{in}}\). This is an external contraction premise; \(c\), \(h_T\), and \(h_\pi\) do not by themselves yield a strict \(\Gamma_m<1\).

### `joint_terminal_certificate`

**Standard consequence, proposed, conditional on Contraction.**

\[
\boxed{
\max\{0,D_{\mathrm{ref}}-2\varepsilon_m\}
\le D_{\mathrm{obs}}
\le D_{\mathrm{full}}
\le U_m.
}
\]

Proof: the first inequality is the observed lower bound; the second is TV data processing under the stochastic observation matrix \(J\); the last is the independent contraction hypothesis. Standard channel-contraction results justify data processing but do not establish a strict coefficient for this particular model. ([Polyanskiy–Wu](https://people.lids.mit.edu/yp/homepage/data/simple-IMA.pdf))

There are two different consequences:

- **`reference_contraction_compatibility`:** Necessarily \(D_{\mathrm{ref}}\le U_m+2\varepsilon_m\). A separately asserted lower bound \(D_{\mathrm{ref}}\ge s_m\) contradicts the other premises if \(s_m>U_m+2\varepsilon_m\); it does not identify which premise was wrong.
- **`no_terminal_decoder_of_contraction`:** If \(U_m<1-p_0-p_1\), no decoder using the complete terminal state can achieve both individual targets. This includes randomized decoders and therefore also rules out decoders restricted to \(Y\).

For the second consequence, any complete-state decoder obeys

\[
e_0+e_1\ge1-D_{\mathrm{full}}\ge1-U_m.
\]

Thus \(U_m<1-p_0-p_1\) forces \(e_0>p_0\) or \(e_1>p_1\). The strict inequality matters: equality of the thresholds alone gives no impossibility conclusion.

A lower bound on reference distinguishability is not needed for this no-decoder result. Conversely, the reference-error transfer certificate needs no contraction theorem.

### Expanded complete-state version

If the actual complete state is larger than \(V\), do not call a contraction on \(V\) complete. Instead specify finite complete spaces \(W_0,\ldots,W_m\), common row-stochastic handoff kernels \(K_j:W_j\times W_{j+1}\to\mathbb R\), two probability laws \(\lambda_0^b\), and a common terminal observation kernel \(O_m:W_m\times Y\to\mathbb R\).

Set

\[
\lambda_{j+1}^b=\lambda_j^bK_j.
\]

Require the explicit terminal identification

\[
\boxed{\lambda_m^bO_m=a_b\quad(b=0,1).}
\tag{Alignment}
\]

For \(0\le j<m\), independently assume

\[
\operatorname{TV}(\lambda_{j+1}^0,\lambda_{j+1}^1)
\le\theta_j\operatorname{TV}(\lambda_j^0,\lambda_j^1),
\qquad 0\le\theta_j\le1.
\]

Induction yields

\[
U_m=
\operatorname{TV}(\lambda_0^0,\lambda_0^1)
\prod_{j=0}^{m-1}\theta_j,
\]

and the same sandwich and no-decoder results hold with \(D_{\mathrm{full}}=\operatorname{TV}(\lambda_m^0,\lambda_m^1)\). For \(m=0\), the empty product is one; Alignment remains a hypothesis.

A bound only for a selected codebook at step zero cannot be iterated without showing it applies to each propagated pair. A global Dobrushin coefficient is sufficient but stronger than necessary; it is defined by the maximum TV distance between two rows of the relevant kernel. ([Dobrushin characterization](https://people.lids.mit.edu/yp/homepage/data/simple-IMA.pdf))

Alignment must be proved, not inferred from common labels or intended behavior. If only approximate alignment is available, an additional observation-error budget must be added; the exact-alignment theorem must not be reused unchanged.

### Complete-state accounting constraints

All channels must be the same under both alternatives; information about the label may enter through the initial complete-state laws, not through an uncounted label-dependent controller. Fresh label-independent randomness can be integrated into a stochastic kernel, while label-correlated ancillary state must be included in the joint preparation.

A decoder using an entire observation history is outside a terminal-state claim unless that accessible history is part of \(W_m\) or the observation object is changed accordingly. A protected retained copy may make strict complete-channel contraction false; it cannot simply be excluded to obtain a desired coefficient.

## Exact horizon scope

The conclusion concerns the terminal event

\[
\{d(Y_m)\ne b\}
\]

under each preparation. The existing \(T^m\) formulation assumes one fixed, time-homogeneous kernel \(T\); the separate time-varying \(K_j\) contraction extension does not automatically generalize the kernel-closure theorem to time-varying coarse models.

The specification does not establish any of the following:

- **Whole-execution correctness:** Every intermediate logical state or answer is correct.
- **Path-law approximation:** Actual and reference distributions of \((Y_0,\ldots,Y_m)\) are close.
- **Permanent preservation:** Every input distinction remains decodable at every later time.
- **A failure deadline:** Actual errors exceed the target when the sufficient horizon inequality ceases to hold.

If compatible per-time error events \(F_j\) are separately defined on one execution probability space and \(\Pr(F_j\mid b)\le p_{j,b}\) is proved, then a union bound gives

\[
\Pr\!\left(\bigcup_{j=0}^{m}F_j\mid b\right)
\le\sum_{j=0}^{m}p_{j,b}.
\]

This additional argument needs no independence, but does need those per-time semantic events and bounds. Terminal marginal accuracy at step \(m\) alone does not supply them.

## Required regression cases

### Exact closure with an information-erasing observation

Take \(V=\{0,1\}\), \(T=I_2\), \(\pi=(1,2)\), and the one-cell partition \(Y=\{\ast\}\). Then

\[
J=\begin{pmatrix}1\\1\end{pmatrix},\qquad Q=(1),
\qquad C=0,\quad c=0,\quad\varepsilon_m=0.
\]

Choose \(\mu_0=(1,0)\), \(\mu_1=(0,1)\). At every \(m\),

\[
a_0=a_1=r_0=r_1=(1),\qquad
D_{\mathrm{ref}}=D_{\mathrm{obs}}=0,\qquad
D_{\mathrm{full}}=1.
\]

Expected assertions:

- **Exact TV conversion:** \(\operatorname{TV}(a_b,r_b)=0\) for both labels.
- **Exact error transfer:** Actual and reference errors agree for every fixed decoder.
- **No useful observed decoder:** A deterministic decoder has errors \((0,1)\) or \((1,0)\); a randomized decoder outputting one with probability \(t\) has errors \((t,1-t)\).
- **No false completeness inference:** Perfect full-state decoding remains possible; observation destroyed the distinction, not the identity dynamics.

This case must prevent any theorem of the form “zero closure defect implies low decoding error.” Its reference-error premise fails for a target below \(1/2\), even though all approximation bounds are exact.

### Average error differs from worst conditional error

Take \(V=Y=\{0,1\}\), the discrete partition \(J=I_2\), \(T=I_2\), and any strictly positive reference weights. Then \(Q=I_2\), \(c=0\), and actual and reference laws coincide.

Choose

\[
\mu_0=(1,0),\qquad \mu_1=(1/2,1/2).
\]

Their TV distance is \(1/2\). A randomized decoder is specified by \(r=\Pr(d=1\mid y=0)\) and \(s=\Pr(d=1\mid y=1)\), yielding

\[
e_0=r,\qquad e_1=1-\frac{r+s}{2}.
\]

Increasing \(s\) to one cannot worsen either error. At \(s=1\), the errors are \(r\) and \((1-r)/2\).

Expected assertions:

| Objective | Optimum | Achieving decoder |
|---|---:|---|
| Equal-prior average error \((e_0+e_1)/2\) | \(1/4\) | \(r=0,\ s=1\) |
| Worst conditional error, allowing randomization | \(1/3\) | \(r=1/3,\ s=1\) |
| Worst conditional error, deterministic decoders only | \(1/2\) | \(r=0,\ s=1\) |

At \(p=1/4\), the necessary bound \(D_{\mathrm{obs}}\ge1-2p\) holds with equality, but no decoder achieves both \(e_0\le p\) and \(e_1\le p\). The optimum-average decoder has errors \((0,1/2)\), not \((1/4,1/4)\).

### Normalization, nonstationarity, and boundary checks

Additional small regressions should protect the interface:

- **Half-\(L^1\) normalization:** For \(a=(1,0)\), \(r=(0,1)\), the \(L^1\) distance is \(2\), TV is \(1\), and the event-probability difference on \(\{0\}\) is \(1\). This tests the sharp generic conversion factor.
- **Nonstationary reference weights:** Let \(T=\begin{pmatrix}0&1\\1&0\end{pmatrix}\), \(\pi=(1,2)\), and \(J=I_2\). Then \(\pi T=(2,1)\ne\pi\), but \(Q=T\), \(c=0\), and all exact-transfer statements still hold.
- **Terminal step zero:** For arbitrary admissible \(T,P,\pi,\mu_b\), \(a_b=r_b=\mu_bJ\) and \(\varepsilon_0=0\). Initial observed distinguishability still requires a separate assumption.

All regression values above are direct finite calculations proposed as future tests. They are not reported as already-compiled Lean examples.

## Proof obligations and proposed implementation order

| Item | Status | Required justification |
|---|---|---|
| \(Q\) stochastic and \(\|E_m\|_{\mathrm{row}}\le mc\) | Existing | `coarseKernel_isStochastic`, `kernel_closure_error_le` |
| Probability propagation through rectangular kernels | Standard consequence, proposed | Nonnegative finite sums and row normalization |
| Half-\(L^1\) TV conversion | Standard consequence, proposed | Probability-vector row norm inequality |
| Fixed decoder's individual error transfer | Standard consequence, proposed | TV event or bounded-test inequality |
| Observed-distinguishability lower bound | Standard consequence, proposed | Triangle inequality |
| Complete-channel sandwich and no-decoder corollary | Standard consequence, proposed, conditional | Data processing plus an independently established contraction |
| Input laws represent the required semantic alternatives | External obligation | Encoding and task specification |
| Reference decoder meets \(\beta_0,\beta_1\) | External obligation | Independent semantic correctness or reliability theorem |
| \(T\) represents the actual experiment | External obligation | State/model identification; closure only compares two laws derived from \(T\) |
| State is complete and Markov at the chosen level | External obligation | Controller, memory, redundancy, observations, and noise accounting |
| Strict \(\Gamma_m\), or applicable \(\theta_j\) | External obligation | Model-specific contraction proof |
| Expanded-model Alignment | External obligation | Exact agreement with the laws used by the kernel certificate |
| Any continuum, scale, bandwidth, dissipation, or fluid interpretation | Outside this specification | Separate instantiation and approximation theorems |

The dependency order should be: probability propagation and TV lemmas; kernel-to-TV conversion; fixed-decoder terminal reliability; observed separation; independent complete-channel compatibility; then the regression cases. No stationarity assumption is needed anywhere in this specified theorem package.

The resulting certificate deliberately separates three conclusions: a reference decoder's reliability transfers within a certified approximation budget; an upper complete-state distinguishability bound can rule out all terminal decoders; and expiration of the approximation guarantee establishes neither success nor failure. That separation is the intended contract for a later application.
