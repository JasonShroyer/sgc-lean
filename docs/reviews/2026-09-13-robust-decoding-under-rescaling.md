# Robust decoding under rescaling: an SGC audit and theorem framework

## Scope and verification

This assessment separates three obligations: preserving the semantics of a computation, controlling an approximate predictor, and proving that a specified physical realization keeps the relevant alternatives distinguishable. The concrete starting point is `JasonShroyer/sgc-lean`, branch `opus/two-horizons`, at commit `c8dee8cd7c899d105386f7981c76b896a985b7af`; the cited handoff and horizon source files were inspected directly. This is a read-only source audit and mathematical derivation, not an independent Lean rebuild or a change to the formalization. ([Committed handoff source](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Bridge/DeterministicKernels.lean), [committed kernel horizon source](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

### What the bare theorem actually establishes

The definitions are

\[
X=C\times\{\mathrm{false},\mathrm{true}\},\qquad
H(c,b)=(S(c),\mathrm{true}),\qquad
a(c,b)=\mathbf1_{\{b=\mathrm{true}\}}.
\]

The theorem proves \(\operatorname{fst}\circ H=S\circ\operatorname{fst}\) and \(a(H(c,\mathrm{false}))=a(c,\mathrm{false})+1\), exactly as stated in the source. There is no conserved total energy, donor energy account, metric, perturbation model, or decoder-error condition in the statement. ([`bare_two_level_compatible`](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Bridge/DeterministicKernels.lean))

Two further scope corrections matter:

- **Arbitrary configuration type:** The theorem quantifies over `C : Type*`, without a `Fintype C` hypothesis; the finiteness assumptions on the preceding permutation theorems do not constrain this separate declaration. ([Lean statement](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Bridge/DeterministicKernels.lean))
- **Exact simulation, not injective information preservation:** `S : C → C` is arbitrary and may erase distinctions, even by being constant; the commuting equation therefore expresses faithful advancement of the declared program semantics, not recoverability of the preceding program state. ([Lean statement](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Bridge/DeterministicKernels.lean))

The appropriate interpretation is an algebraic consistency check. It does not establish compatibility between robust computation and physical energy transfer.

## Robustness must specify the protected information

### The primary robustness theorem does not follow from a local margin

CMPP Remark 5.3 explicitly acknowledges the fragility of its generalized-shift encoding, states that robust computation can be obtained on noncompact spaces, and cites Bournez–Graça–Hainry for a compact-domain obstruction. It is a warning about the robustness of the computational simulation, not a theorem identifying viscosity with tape noise. ([CMPP, Remark 5.3](https://pmc.ncbi.nlm.nih.gov/articles/PMC8126859/))

The pertinent primary result is Theorem 16 of Bournez–Graça–Hainry, “Computation with perturbed dynamical systems”: if a language is robustly accepted by a system on \([-1,1]^d\) with Lipschitz, computable dynamics and the paper's input/output interface, that language is recursive. The compact result concerns acceptance, so nonmembers may continue computing forever; it is not restricted to machines that explicitly reject every nonmember. ([BGH, Definitions 7–12 and Theorem 16](https://inria.hal.science/hal-00643634v1/document))

The hypotheses need to be preserved rather than replaced by a margin slogan:

| Feature | Primary-source condition and relevance |
|---|---|
| Perturbations | Discrete trajectories satisfy \(\|x_{j+1}-f(x_j)\|\le\epsilon\); continuous trajectories satisfy \(\|\dot x-f(x)\|\le\epsilon\). These are trajectory perturbations, not a tracer-diffusion model. ([BGH, Definition 10](https://inria.hal.science/hal-00643634v1/document)) |
| Robustness | \(L=L_\omega\), where \(L_\omega=\bigcap_{\epsilon>0}L_\epsilon\) and \(L_\epsilon\) is the paper's perturbed acceptance/recognition language. The paper states that \(L_\epsilon\) grows with \(\epsilon\); this is not simply the assertion that one fixed positive radius makes every perturbed trajectory a faithful configuration-by-configuration simulation. ([BGH, Lemma 11 and Definition 12](https://inria.hal.science/hal-00643634v1/document)) |
| Observation interface | Computable compute/accept/reject regions, with separation and accessibility requirements, are part of the setup. A current-symbol decoder and a dimensionless local tolerance do not themselves establish this language-level interface. ([BGH, Definition 7](https://inria.hal.science/hal-00643634v1/document)) |
| Unbounded counterpart | Theorems 17–18 on \(\mathbb R^d\) require robust recognition, which in this paper means deciding: members eventually accept and nonmembers eventually reject. They should not be paraphrased as excluding robust simulation of arbitrary Turing machines on unbounded spaces. ([BGH, Definition 7 and Theorems 17–18](https://inria.hal.science/hal-00643634v1/document)) |
| Positive counterexample | BGH Theorem 19 states robust Turing-machine simulation by analytic computable ODEs on \(\mathbb R^6\), with perturbation tolerance \(\epsilon\le1/4\); the Graça–Campagnolo–Buescu construction encodes tape information using unbounded numerical coordinates. Uniform absolute robustness therefore need not exclude universality when the storage resource is noncompact. ([BGH, Theorem 19](https://inria.hal.science/hal-00643634v1/document), [Graça–Campagnolo–Buescu](https://sqigmath.tecnico.ulisboa.pt/pub/GracaDS/06-GCB-Poly.pdf)) |

For formalization, even the region-separation condition needs an explicit convention: the BGH text calls it nonzero “Hausdorff distance,” but ordinary positive Hausdorff distance between two sets is not, by itself, a uniform decoder buffer. A usable robustness specification should declare the actual distance from valid encoded states to the wrong-decision region, rather than inherit ambiguous terminology. ([BGH, Definition 7](https://inria.hal.science/hal-00643634v1/document))

The conclusion is limited but decisive: \(\inf_n\widehat\delta_n>0\) alone does not trigger Theorem 16. Applicability requires a reduction from the proposed multiscale model to the paper's fixed-domain, effective, robust language-acceptance model; varying metrics, growing resources, and the perturbation quantifiers are substantive parts of that reduction.

### Local readout is not an indefinitely reliable tape

Consider the following explicit symbolic example, independently of any fluid construction. On binary sequences, use

\[
d(s,t)=\sum_{i\in\mathbb Z}2^{-|i|-2}\mathbf1_{\{s_i\ne t_i\}},
\qquad P(s)=s_0.
\]

Every perturbation of distance strictly less than \(1/4\) preserves the current decoded symbol, because changing coordinate zero alone costs \(1/4\). Thus this local decoder has a uniform positive tolerance throughout the entire configuration space.

Nevertheless, for every positive perturbation budget, a sufficiently distant bit can be changed within that budget. Under repeated left shifts, the altered bit eventually reaches coordinate zero. Uniform robustness of current-symbol readout therefore does not imply preservation of every symbol that will be needed later, even for a simple tape transport.

There is also a separate packing obstruction. In one totally bounded metric space, an infinite family of codewords cannot have a common positive lower bound on pairwise separation: a finite cover by balls of radius less than half that bound would have room for at most one codeword per ball. Requiring uniform pairwise separation of all complete configurations would therefore exclude unbounded robust storage by assumption, rather than reveal a fluid-specific obstruction.

For arbitrary metric spaces, a decoder-ball condition and pairwise separation should not be identified without checking the geometry. The packing conclusion applies directly when distinct semantic codewords must remain distinct under all allowed perturbations of a fixed radius.

### Resource accounting and quantifiers

A useful definition should declare all of the following before a no-go theorem is attempted:

- **Semantic obligation:** Is the output the currently read symbol, the next control state, a final answer, or the entire tape? Two histories may legitimately merge once no future required answer distinguishes them.
- **Noise quantifier:** Does robustness concern one initial perturbation, bounded adversarial errors at every step, a stochastic law, or perturbations of the vector field itself?
- **Reliability horizon:** Is the guarantee per read, for the final output after \(N\) steps, or for every read up to \(N\) simultaneously?
- **Resource family:** Do occupied volume, number of cells, effective dimension, amplitudes, redundancy, or controller memory grow with the input or horizon?
- **Metric and effectiveness:** Are the metric, decoder, rescaling, and promised tolerances uniformly computable, and in what physical units is the perturbation bounded?

Bounding the number of decoded labels is not the same as imposing physical spectral bandwidth. A bandwidth hypothesis needs a specified domain, basis or frequency cutoff, amplitude norm, and rescaling convention; a finite alphabet or a fixed number of coarse labels supplies none of these by itself.

For example, if conditional failure probabilities at successive required reads are bounded by \(p_j\), a union bound gives

\[
\Pr(\text{any failure through step }N)\le\sum_{j<N}p_j.
\]

A fixed per-read upper bound is not a fixed all-run guarantee. Summable error budgets can support a uniform all-run bound, but the mechanism that achieves them, such as growing redundancy or improved control, must be included in the resource account; the union bound alone proves no necessity theorem.

## What scaling does and does not settle

### The rescaling test

The following calculations use the proposed localized three-dimensional rescaling

\[
u_q(x,t)=q^{-1}u(x/q,t/q^2),\qquad 0<q<1.
\]

For a correspondingly rescaled region or a localized profile on \(\mathbb R^3\),

\[
\ell_q=q\ell,\quad a_q=q^{-1}a,\quad \tau_q=q^2\tau,
\quad
\frac{\nu\tau_q}{\ell_q^2}=\frac{\nu\tau}{\ell^2}.
\]

Changing variables gives

\[
\|u_q(t)\|_2^2=q\|u(t/q^2)\|_2^2,
\qquad
\|\nabla u_q(t)\|_2^2=q^{-1}\|\nabla u(t/q^2)\|_2^2.
\]

Consequently, the viscous energy dissipated during a corresponding stage also scales by \(q\). Neither the energy identity nor dimensional analysis alone forces the ratio of stage dissipation to stage energy to worsen.

For geometric handoffs, durations proportional to \(q^{2n}\) and packet energies proportional to \(q^n\) are summable. This is an accounting consistency check, not the construction of a Navier–Stokes solution, an executable fluid computer, or a mechanism transferring energy between those packets.

Scale invariance also does not prove that computation survives. A scale-independent loss factor strictly below one can compound over infinitely many stages; what is missing is a justified estimate for that loss on the relevant information channel.

There is an especially clean information-theoretic version of this point. For an invertible measurable rescaling with measurable inverse, total variation is unchanged by pushing both laws through that rescaling, because the measurable events in the defining supremum correspond bijectively. A loss of distinguishability must therefore enter through the dynamics, a noninvertible observation, or a noise channel, not through a mere change of units.

### The margin must follow its own norm

For velocity perturbations \(w_q(x)=q^{-1}w(x/q)\), direct changes of variables give

\[
\|w_q\|_{L^p}=q^{3/p-1}\|w\|_{L^p},
\qquad
\|w_q\|_{\dot H^s}=q^{1/2-s}\|w\|_{\dot H^s}.
\]

Thus a positional tolerance scales by \(q\), a velocity \(L^\infty\) tolerance by \(q^{-1}\), and a velocity \(L^2\) tolerance by \(q^{1/2}\). Dividing every margin by \(\ell\) would conflate physically different notions of perturbation; the normalized state and metric should be specified first.

### Tao is a control for the hypotheses, not a robustness theorem

Tao's averaged model preserves the energy cancellation \(\langle\widetilde B(u,u),u\rangle=0\) and the energy identity, while retaining broad families of the usual harmonic-analysis estimates; nevertheless, it has finite-time blowup. A universal obstruction derived only from properties shared with this model must also be checked on that counterexample. ([Tao's announcement](https://terrytao.wordpress.com/2014/02/04/finite-time-blowup-for-an-averaged-three-dimensional-navier-stokes-equation/), [original paper](https://arxiv.org/pdf/1402.0290v3))

Tao specifically points to structure absent from the averaged equation, including the genuine Navier–Stokes vorticity formulation using differential rather than pseudodifferential operators. That is a candidate place to seek a new estimate, not an already-proved inequality linking decoding margin to dissipation. ([Tao's discussion of the additional structure](https://terrytao.wordpress.com/2014/02/04/finite-time-blowup-for-an-averaged-three-dimensional-navier-stokes-equation/))

The proposed \(a\sim\ell^{-1}\), \(\tau\sim\ell^2\) accounting should also not be mistaken for the unique possible cascade. Tao's concentrated, nearly energy-preserving cascade has transition times approximately \(\ell^{5/2}\), faster than the diffusive time \(\ell^2\), and the construction survives hyperdissipation below the \(5/4\) threshold; the exact stage behavior is not the same as a self-similar packet with energy proportional to \(\ell\). ([Tao, cascade mechanism and dissipation comparison](https://arxiv.org/pdf/1402.0290v3))

The reviewed sources supply no general Navier–Stokes-specific estimate forcing deterioration of a scale-normalized decoder margin after accounting for recovery. This is an identified missing bridge, not a claim that no restricted-model theorem can exist or that a general impossibility has been proved.

### A stability estimate is not a forced-loss estimate

For two smooth incompressible Navier–Stokes solutions \(u\) and \(u+w\), with the same viscosity and suitable boundary conditions, subtracting the equations and integrating by parts yields

\[
\frac12\frac{d}{dt}\|w\|_2^2+\nu\|\nabla w\|_2^2
=-\int w_iw_j\,\partial_j u_i\,dx.
\]

Bounding the right-hand side in absolute value gives the familiar kind of perturbation upper estimate,

\[
\frac12\frac{d}{dt}\|w\|_2^2
\nu\|\nabla w\|_2^2
\le \|\nabla u\|_{\infty,\mathrm{op}}\|w\|_2^2.
\]

This calculation does not show that an encoding must become undecodable: it is an upper bound on perturbation growth, not a lower bound on semantic error or an upper bound on distinguishability. Furthermore, \(\int_{\mathrm{stage}}\|\nabla u\|_{\infty,\mathrm{op}}dt\) is invariant under the proposed rescaling, so this estimate alone does not produce progressively worse dimensionless stage behavior.

### Viscous smoothing need not contract total variation of field laws

Here is an explicit deterministic counterexample to an unjustified physical-to-information inference. On a periodic domain, the two shear fields

\[
u^\pm(x,y,z,t)
=\pm A e^{-\nu k^2t}\sin(ky)\,e_x
\]

solve the unforced incompressible Navier–Stokes equation with constant pressure: their advective nonlinearity vanishes and their Laplacian is \(-k^2u^\pm\). Their amplitudes and energies decay.

Yet, at every finite time, the fields are distinct. Consequently, the point-mass laws on full velocity fields satisfy

\[
d_{\mathrm{TV}}(\delta_{u^+(t)},\delta_{u^-(t)})=1.
\]

An exact sign measurement still distinguishes them. A finite-resolution or noisy measurement may not, but that requires an observation channel or perturbation model absent from viscosity alone; this example does not claim robustness to fixed-amplitude observational noise.

### A relevant 2025 correction to the viscosity narrative

“Turing complete Navier–Stokes steady states via cosymplectic geometry” proves that a Hodge-admissible Riemannian three-manifold admits a generally non-small metric deformation supporting a Turing-complete stationary Navier–Stokes field for every \(\nu\ge0\). The paper uses the vector-field Hodge Laplacian and constructs harmonic fields with \(\Delta X=0\), so the viscous term vanishes on those fields. ([2025 paper, Theorem A and Proposition 4.1](https://arxiv.org/html/2507.07696v1))

This is Lagrangian universality in stationary fields on the specified geometry, not a noise-tolerant computation theorem, a self-replicating cascade, or a solution of the standard flat-domain blowup problem. The authors explicitly retain the distinction between invariance under changing viscosity and fragility under perturbations; therefore “any positive viscosity destroys fluid computation” is not an acceptable general statement. ([2025 paper, construction and conclusion](https://arxiv.org/html/2507.07696v1))

## A joint certificate already suggested by KernelHorizon

### The existing operator theorem

Let \(T\) be a stochastic matrix on a finite microscopic state space, \(J\) the deterministic matrix recording the chosen partition, and \(Q\) the canonical coarse kernel formed using strictly positive reference weights. The existing theorem, in its maximum-row \(L^1\) norm, is

\[
\|T^mJ-JQ^m\|_{\infty\to\infty}\le mc,
\qquad c=\|TJ-JQ\|_{\infty\to\infty}.
\]

These stochasticity, positivity, and norm conventions are explicit in `KernelHorizon`; stationarity of the reference weights is not a hypothesis of this theorem. ([`kernel_closure_error_le`](https://raw.githubusercontent.com/JasonShroyer/sgc-lean/c8dee8cd7c899d105386f7981c76b896a985b7af/src/SGC/Renormalization/KernelHorizon.lean))

The next consequences are mathematical derivations from that statement, not claims that these corollaries have already been formalized.

### From closure error to decoder reliability

Take two input laws \(\mu_0,\mu_1\) whose required answers remain different at the assessed horizon. Define actual and reference observed laws on the same coarse state space:

\[
a_b=\mu_bT^mJ,\qquad r_b=\mu_bJQ^m,\qquad b\in\{0,1\}.
\]

Multiplication by a probability row vector cannot exceed the maximum row \(L^1\) error. Since total variation is half the \(L^1\) distance for probability vectors,

\[
d_{\mathrm{TV}}(a_b,r_b)\le\varepsilon_m,
\qquad \varepsilon_m=\min\{1,mc/2\}.
\]

For a specified decoder \(d\) whose reference conditional errors are

\[
e_b^{\mathrm{ref}}=r_b\{d(Y)\ne b\},
\]

the defining event bound for total variation gives

\[
\boxed{
e_b^{\mathrm{actual}}\le e_b^{\mathrm{ref}}+\varepsilon_m,
\qquad b=0,1.
}
\]

Thus a sufficient reliability certificate is

\[
\max_b e_b^{\mathrm{ref}}+\varepsilon_m\le p.
\]

The independent semantic obligation is now visible: the reference model must actually implement the required computation and possess a reliable decoder. A small closure defect cannot establish either condition.

### A distinguishability lower certificate

The triangle inequality also gives

\[
\boxed{
d_{\mathrm{TV}}(a_0,a_1)
\ge
d_{\mathrm{TV}}(r_0,r_1)-2\varepsilon_m.
}
\]

This preserves an independently established separation instead of treating accurate coarse prediction as evidence of separation. The simplest regression test is a partition with one cell: its closure can be exact while both alternatives produce the same observed law and observed total variation is zero.

The lower bound alone does not certify both conditional decoder errors. For example, \(\mu_0=\delta_0\) and \(\mu_1=(\delta_0+\delta_1)/2\) have total variation \(1/2\), but no randomized decoder achieves error at most \(1/4\) on both alternatives: writing \(r\) for the probability of declaring label one at observation zero gives errors \(r\) and \((1-r)/2\), whose best possible maximum is \(1/3\).

This distinction is consistent with the standard equal-prior testing identity: minimum average error is \((1-d_{\mathrm{TV}})/2\), which is not a simultaneous bound on both conditional errors. The two-sided necessary bound \(d_{\mathrm{TV}}\ge1-2p\) follows separately from the acceptance-event argument. ([Stanford testing notes](https://web.stanford.edu/class/stats311/OldSyllabi/full_notes.pdf), [Pollard's total-variation notes](http://www.stat.yale.edu/~pollard/Courses/607.spring05/handouts/Totalvar.pdf))

### Why StatisticalHorizon needs an additional conversion

`StatisticalHorizon` proves an abstract operator-norm bound and describes \(L^2(\mu)\) as its intended Koopman setting; it does not assert a uniform bound over every individual encoded state or every probability law. Its source also explicitly excludes a completed fluid instantiation. ([`StatisticalHorizon`](https://github.com/JasonShroyer/sgc-lean/blob/opus/two-horizons/src/SGC/Bridge/StatisticalHorizon.lean))

Suppose a probability reference measure \(\mu\) and input densities \(\rho_b\in L^2(\mu)\) have actually been supplied. If a coarse decoder event has indicator \(g\) in the projection's range, Cauchy–Schwarz converts an \(L^2\) operator error bound \(m\eta\) into the expectation-error bound

\[
|\langle\rho_b,(U^m\Pi-A^m\Pi)g\rangle|
\le
\|\rho_b\|_2\,m\eta\,\|g\|_2.
\]

The density norm is a genuine additional resource-dependent constant. Concentrating an encoding into increasingly small sets can make it large, while point-mass inputs may not have such densities at all; omitting it would silently replace an averaged estimate by a worst-case one.

## Operational impossibility requires a complete channel

Suppose \(\mathcal K_n\) acts on the entire state available to future computation, including stored history, controller state, redundancy, and recovery mechanisms. For a fixed pair of alternatives that must still yield different required answers, assume a verified contraction bound

\[
D_{n+1}\le\theta_nD_n,\qquad
D_n=d_{\mathrm{TV}}(\mu_n^0,\mu_n^1),\quad 0\le\theta_n\le1.
\]

Then induction gives

\[
D_n\le D_0\prod_{j<n}\theta_j.
\]

A decoder with conditional error at most \(p<1/2\) on both alternatives requires \(D_n\ge1-2p\): the event on which it declares zero has probabilities at least \(1-p\) and at most \(p\) under the respective laws. Therefore

\[
\boxed{
D_0\prod_{j<n}\theta_j<1-2p
\quad\Longrightarrow\quad
\text{the specified reliability is impossible at stage }n.
}
\]

This is stronger than expiration of an upper error guarantee. But it remains conditional on deriving the contraction constants for the actual channel and the correct surviving semantic distinction.

The standard global coefficient is Dobrushin's \(\theta(\mathcal K)=\sup_{x,x'}d_{\mathrm{TV}}(\mathcal K(x,\cdot),\mathcal K(x',\cdot))\); the information-theoretic literature supplies its contraction and composition properties, not a fluid-specific bound on its value. ([Polyanskiy–Wu, strong data-processing inequalities](https://people.lids.mit.edu/yp/homepage/data/simple-IMA.pdf))

Important limits of this certificate are:

- **Product, not pointwise strictness:** Merely having \(\theta_n<1\) for every \(n\) does not force the product to vanish. A uniform upper bound below one suffices; so does an appropriate divergent cumulative contraction condition.
- **Observation versus full state:** Failure of one observation channel rules out decoders using that observation, not a controller that still has access to hidden state or past observations.
- **Regeneration versus information creation:** A common recovery channel may restore amplitude or a codeword's shape, but cannot increase total variation of the full input laws. Access to an uncounted copy of the answer changes the assumed channel.
- **Global versus code-restricted bounds:** A global Dobrushin coefficient may be one even when particular pairs contract. A code-restricted estimate must be shown to apply again after each noisy handoff.
- **Physical derivation:** Dissipation, smoothness, or the word “noise” alone is not a proof of a strict contraction coefficient.

A concrete sufficient hypothesis is a common minorization

\[
\mathcal K_n(z,\cdot)\ge\beta_n\rho_n(\cdot)
\quad\text{for every admissible complete state }z.
\]

Writing \(\mathcal K_n=\beta_n\rho_n+(1-\beta_n)\widetilde{\mathcal K}_n\) immediately gives \(\theta_n\le1-\beta_n\). This identifies what must be physically justified: a common information-erasing component that applies to the entire admissible state, not merely to an exposed data bit while a protected controller retains its value.

### The joint feasibility test

When the approximation and contraction certificates refer to the same experiment, they can be combined. Observation is itself a channel, so the resulting bounds have the form

\[
D_{\mathrm{reference}}-2\varepsilon
\le D_{\mathrm{actual,observed}}
\le D_{\mathrm{actual,full}}
\le D_{\mathrm{initial,full}}\prod_j\theta_j.
\]

If the leftmost quantity exceeds the rightmost, the asserted reference separation, approximation accuracy, and complete-channel contraction cannot all hold. This identifies a precise conditional incompatibility theorem without presupposing either information loss or survival.

## Recommended research decision

The next target should be a semantic certificate before a physical no-go theorem. Establish a reference decoder's correctness, transfer its conditional-error bounds through the finite-kernel closure estimate, and state separately the physical assumptions that yield any contraction of the complete state.

Three counterexamples should accompany that specification: exact closure with an information-erasing observation, robust current-symbol readout with corrupted future tape, and dissipative deterministic evolution without total-variation loss. Together they prevent the certificate from treating predictive agreement, a local margin, and energy decay as interchangeable.

A fluid-specific contribution would then have a precise location: proving a contraction, observation-noise, packing, or resource estimate from an explicit Navier–Stokes handoff model, with constants that remain valid under its declared rescaling. Finding that the proposed physical assumptions do not imply such an estimate would also resolve the proposed obstruction in that regime.
