# Two Horizons: Redirected Review and Pinned-Commit Audit

Technical review for Jason Shroyer and the SGC project, 12 September 2026. Audit target: `JasonShroyer/sgc-lean`, commit `0096f90e5e5b5fdbdb5209b51cf5c25825183ff9`, on the `opus/two-horizons` lineage.

Reviewer: Perplexity Computer, AI-assisted technical review. This document records source inspection, evidence checks, and mathematical analysis, not independent human expert endorsement.

The revised program has two defensible attachment points: validated approximate solutions, and statistical coarse prediction with an explicit closure error. Neither requires a computation-versus-collapse phase picture. The Bernoulli tower is a valid exact-lumpability example, but its identification with Moore’s Turing simulation is not established by its definitions.

## Scope and verification status

This review inspected the pinned checkout, its paper and claim map, the specified source modules, and the three stored receipts. It independently recomputed receipt self-hashes and statement hashes, compared candidate fields with saved raw probe output, and compared shipped source blobs with the commit recorded by the main receipt. No Lean, Lake, project macros, or project audit code was executed; no repository files were changed.

Accordingly, this is a **source-and-receipt audit, not a fresh build or independent kernel replay**. Statements below described as findings from the checkout refer to that immutable source snapshot; mathematical deductions are explicitly distinguished from already formalized results.

| Check | Finding |
|---|---|
| Checkout identity | Exact requested commit; working tree clean |
| Tracked file count | 53 files, rather than the 49 stated in the commission |
| Receipt self-hashes | All three match sorted-key, compact JSON canonicalization with `hash_self` excluded |
| Stored statement hashes | All match: 170 entries in `opus-closure`, 6 in `abstract-bkm`, 4 in `residual-horizon`; these are receipt entries, not 180 distinct theorems |
| Saved probe consistency | Candidate statements, binders, unused hypotheses, definition cones, and axiom names agree with their saved `@@THM` records |
| Main axiom result | 168 of 170 closures are contained in the standard base; exactly 151 equal all three standard axioms |
| Remaining standard-base closures | 8 use `{propext, Quot.sound}`; 6 use no axioms; 2 use `{propext}`; 1 uses `{Classical.choice}` |
| Project-axiom exceptions | The two documented `SGC.Approximate` theorems consume the three documented extra axioms |
| Supporting inventory | 38 recorded axioms; this count is reproduced from the receipt, not from a fresh elaborated environment |
| Receipt failures | The three `fail` findings are precisely the three extra-axiom dependencies of those two documented exceptions |
| Fresh build / kernel replay | Not performed here; also explicitly skipped or unverified in the receipts |

### Source binding: substantially recoverable, but not complete

The main receipt records clean development commit `0012a5a5b16f7e4e26465e84c3772627a17a5fd0`, not the audited orphan-branch commit. A read-only Git-tree comparison found 33 identical blobs among 36 shipped Lean/build-configuration files: all 31 pre-existing `src/SGC/...` module files, `lean-toolchain`, and `lake-manifest.json`. The curated `src/SGC.lean` root and `lakefile.lean` differ, and `ResidualHorizon.lean` is absent from that older commit.

This is useful positive evidence of module-source identity, not an olean-provenance guarantee. The abstract-BKM receipt records a dirty checkout at `df242c3682f33f198bb70c3f892a124664188cda` but the same aggregate source-tree hash as the main receipt; the residual receipt records a dirty checkout at `0012a5a...` with a different tree hash. A dirty worktree is not reconstructible from its commit identifier alone.

There is also a concrete statement mismatch. In the residual receipt, both the candidate and raw probe statement for `within_tolerance_of_residual_small` contain the explicit hypothesis `hT : 0 ≤ T`; the pinned source at `ResidualHorizon.lean:132–145` omits it. The receipt marks `hT` unused, so this is consistent with harmless post-audit cleanup, but **the stored receipt is not a byte-exact certificate of the current declaration**.

The appropriate eventual repair is to regenerate receipts against the final immutable checkout after a clean isolated build, with per-file source binding and recorded build provenance. A self-hash establishes internal integrity, not an external signature; a statement hash does not by itself pin the bodies of definitions appearing in that statement. No conclusion here alleges a false proof or an undisclosed axiom.

## Certified intervals: a sound horizon, not automatically a resolution detector

### Verdict

**Known completeness for CCRT; lifespan exhaustion follows for a precise supremal certificate; raw monotonicity is not established.** Morosi–Pizzocchero already convert approximate-solution residuals and initial-data error into an existence interval and an error enclosure, including the explicit Galerkin residual in equation (6.20); CCRT additionally prove eventual success of their test for sufficiently fine Galerkin approximations whenever the strong solution exists on a fixed interval ([Morosi–Pizzocchero](https://arxiv.org/html/1104.3832v1); [CCRT, Theorem 8](https://arxiv.org/pdf/math/0607181v2)).

The useful definition is a **certified existence horizon**, accompanied by a separate **certified accuracy horizon**. Neither is canonically a function of \(N\) and the numerical trajectory alone: the target initial data, forcing, unresolved tails, norm, estimator constants, and validation protocol must be specified. These are substantive inputs to the cited a posteriori estimates, not merely implementation details ([Morosi–Pizzocchero, Sections 3–4 and 6](https://arxiv.org/html/1104.3832v1)).

### The two residuals still must not be merged

For \(B(a,b)=\mathbb P((a\cdot\nabla)b)\), the lifted Galerkin trajectory has full-equation residual

\[
r_N=\dot v_N+\nu Av_N+B(v_N,v_N)-f
     =(I-P_N)\bigl[B(v_N,v_N)-f\bigr].
\]

This is computable from an adequately validated approximation and forcing description; the initial discrepancy \(u_0-v_N(0)\) remains part of the certificate. It is exactly the residual structure used by Morosi–Pizzocchero, with their opposite sign convention for the bilinear operator ([equation (6.20)](https://arxiv.org/html/1104.3832v1)).

By contrast, the residual of the unknown projected true solution \(P_Nu\) in the Galerkin vector field is

\[
-R_N(u),\qquad
R_N(u)=P_N\bigl[B(u,u)-B(P_Nu,P_Nu)\bigr].
\]

This identity is an elementary subtraction of the two equations. It does not make \(R_N(u)\) available from \(v_N\) alone. A theorem using \(R_N\) along the true solution is not, without additional enclosures, a computable a posteriori certificate.

### Monotonicity and completeness have different quantifiers

Nested approximation spaces do not order the nonlinear trajectories, their residual estimators, or their stability coefficients. Therefore the fact that a certificate is sound gives no inequality \(T_{\mathrm{cert}}(N+1)\ge T_{\mathrm{cert}}(N)\). Even a valid certificate may be deliberately shortened; monotonicity is not a property of “being certified.”

In the periodic, mean-zero setting, CCRT Theorem 8 states that for \(m\ge3\), \(u_0\in V^m\), \(f\in L^1(0,T;V^m)\cap L^2(0,T;V^{m-1})\), and an existing strong solution, “there exists an \(N\)” such that the Galerkin solution passes condition (21) “for every \(n\ge N\)” ([CCRT, Theorem 8](https://arxiv.org/pdf/math/0607181v2)). Its Corollary 9 treats time-discrete interpolants with the requisite trajectory and derivative convergence; spatial refinement alone does not supply those numerical hypotheses ([CCRT, Corollary 9](https://arxiv.org/pdf/math/0607181v2)).

Thus the decisive quantifier is already known in this setting:

\[
\forall T<T^*,\quad
\text{eventually the validation procedure certifies existence through }T.
\]

For smooth target data and forcing, define the ideal CCRT endpoint precisely by
\[
T_N^{\mathrm{CCRT}}
=\sup\{T>0:\text{condition (21) passes for }v_N
                  \text{ and the target data on }[0,T]\}.
\]
Take the supremum of the empty set to be zero. Soundness gives \(T_N^{\mathrm{CCRT}}\le T^*\), and Theorem 8 gives \(\liminf_N T_N^{\mathrm{CCRT}}\ge T\) for every \(T<T^*\); hence
\[
\boxed{T_N^{\mathrm{CCRT}}\longrightarrow T^*.}
\]
This is a direct corollary derived here from CCRT’s fixed-interval result, not a separately named theorem in that paper ([CCRT, Corollary 5 and Theorem 8](https://arxiv.org/pdf/math/0607181v2)). It does not require per-\(N\) monotonicity.

For a Morosi–Pizzocchero implementation, the analogous sufficient-condition argument is as follows. Fix \(T<T^*\), suppose initial-error and time-integrated residual estimators tend to zero, and suppose the control-equation coefficients stay uniformly bounded on \([0,T]\); the scalar comparison equation then admits a small enclosure through \(T\) for sufficiently accurate approximations. These are the relevant estimator hypotheses, and they must be checked rather than inferred from the name of the certificate ([Morosi–Pizzocchero, control inequalities (4.24)–(4.27)](https://arxiv.org/html/1104.3832v1)).

An arbitrary conservative estimator, fixed time discretization, or unresolved-tail bound that never improves can destroy completeness without contradicting soundness. This distinction is substantive: Dashti–Robinson also prove eventual Galerkin verification, whereas a recent finite-element criterion explicitly leaves its corresponding residual-convergence/verifiability question unresolved ([Dashti–Robinson, Theorem 6.1(ii)](https://arxiv.org/pdf/math/0701341); [a posteriori strong-solution verification, 2025](https://ar5iv.labs.arxiv.org/html/2509.25105)).

A monotone lower approximation can instead be defined by construction. Enumerate validated certificates with endpoints \(T_j\), including spatial resolution, time precision, and any restart choices, and set

\[
\underline T_m=\max_{j\le m}T_j.
\]

Soundness and cofinality, \(\forall T<T^*\,\exists j:T_j>T\), imply
\(\underline T_m\uparrow T^*\). This is an elementary order argument; it does not provide an upper bound on \(T^*\), a computable convergence rate, or a decision procedure for blowup. Effective enumeration additionally requires effective descriptions and certified bounds for the data, not merely the adjective “smooth.” The ideal supremum defining \(T_N^{\mathrm{CCRT}}\) should not itself be declared an exactly computable real without a further argument; a finite validated endpoint and an exact optimal endpoint are different objects.

### The proposed successor to Conjecture 6.2 still fails

“Every fixed certificate stops below \(T^*\)” does not imply that physical resolution must diverge. Certificates are sufficient tests and may be conservative; for a globally regular zero solution, deliberately reporting the valid intervals \([0,N]\) produces finite certificates at every \(N\), although one spatial resolution is exact forever. This illustrates the ambiguity of an unspecified reporting procedure, not the behavior of the ideal CCRT supremum for the zero solution. For a finite singular time, every closed interval on which smooth existence is certified must already end before that time, so this condition alone adds no resolution information; moreover, the supremum of such endpoints can equal \(T^*\) without being attained.

More decisively, the replacement in `two-horizons.md:429–438` asks for projected Galerkin tracking at **every** tolerance. In the unforced energy-bounded setting, with \(\|u(t)\|_2,\|v_N(t)\|_2\le M\),

\[
\|P_Nu(t)-v_N(t)\|_2\le 2M
\]

for every cutoff and time of existence. Thus a tolerance greater than \(2M\) cannot force any resolution to escape, even conditionally on a finite-energy singularity. At any chosen fixed cutoff, equivalence of finite-dimensional norms gives the same large-tolerance obstruction for projected Sobolev norms. If \(T^*=\infty\) is not explicitly excluded, a nonzero steady finite-Fourier Euler solution supplies an additional literal counterexample: its infinite-time vorticity integral diverges while a fixed Galerkin representation is exact.

A defensible replacement uses **full-state approximation in a continuation-controlling norm**, not projected \(L^2\) tracking. For example, assume:

- **Finite singular time:** \(T^*<\infty\) and \(\|u(t)\|_{H^s}\to\infty\) as \(t\uparrow T^*\).
- **Bounded fixed approximations:** every fixed \(v_N\) stays bounded in \(H^s\) on \([0,T^*)\).
- **Pre-singular completeness:** for every \(t<T^*\), some \(N\) approximates the full trajectory within \(\eta\) in \(C([0,t];H^s)\).

Define
\[
N_\eta(t)=\min\left\{N:
 \sup_{0\le r\le t}\|u(r)-v_N(r)\|_{H^s}\le\eta\right\}.
\]
Then \(N_\eta(t)\to\infty\): the triangle inequality eventually excludes each of the finitely many cutoffs \(N\le K\), for every \(K\). This short proof is about approximation in a norm that blows up. It is not a defect criterion, not a determining-wavenumber identity, and not automatically a statement about a computable certificate.

### What `ResidualHorizon` actually adds

The new module is already **inhomogeneous in the error comparison**: its bound contains the additive residual size \(\varepsilon\). The distinction from the recommended energy estimate is not “homogeneous versus any additive forcing”; it is uniform two-sided Lipschitz control and a constant residual bound versus a time-dependent, one-sided energy estimate with explicit initial error.

It assumes both trajectories on \([0,T]\), including continuity through the endpoint, and proves their closeness there. It proves no new existence interval or continuation theorem. Its zero-residual theorem establishes exact tracking on each interval satisfying those hypotheses, not existence for infinite time; the explicit exponential quotient requires \(K\ne0\), with the \(K=0\) case supplied by the general `gronwallBound`.

## The computation axis: a Bernoulli tower, not Moore’s machine

### Verdict

**The identification is false; the actual lumpability theorem remains valid in its narrower scope.** The pinned `shiftKernel` is a finite-word transition kernel that drops the oldest symbol and appends a uniformly random fresh symbol. `shiftTower_defect_zero` states zero row-sum approximate-lumpability error for that kernel and `tailPartition`; it does not mention a Turing machine, a machine configuration, an encoding, or a halting predicate.

The correct replacement for Theorem 2.5 is: **“Uniform fresh-symbol shift kernels form an exactly lumpable tower under deletion of the oldest symbol.”** “I.i.d.-input symbolic dynamics is renormalization-transparent” is an acceptable explanatory description, provided the paper distinguishes the proved finite-kernel identity from a still-unformalized product-measure realization. It cannot remain a theorem about “the pole where computation lives.”

### What the definitions decide

The decisive source locations are `CantorShiftTower.lean:81–111, 200–230, 302–321`. `Word p n` is `Fin n → Fin p`; `shiftIn` advances the window using an explicitly supplied symbol; `shiftKernel` averages over that symbol; `pathShift` is the ordinary one-sided shift on `ℕ → A`.

The theorem `truncate_pathShift` says
\[
\operatorname{truncate}_n(\sigma x)
 =\operatorname{tail}(\operatorname{truncate}_{n+1}x).
\]
This uses **one more input symbol**, not an autonomous depth-\(n\) deterministic update. Two infinite paths with the same first \(n\) symbols and different next symbols give different next windows. The identity is correct and useful, but it does not fill that information gap.

For \(p\ge2\), after \(n\) steps the finite kernel has replaced every initial symbol by fresh uniform input; its \(n\)-step transition law is independent of the initial word. This follows directly from the definition and is not asserted to be a new Lean theorem. The stochastic interpretation requires \(p>0\), exactly as `shiftKernel_row_sum` requires `[NeZero p]`; the algebraic zero-defect theorem is also stated for degenerate alphabet sizes.

“Odometer / Bernoulli shift” should also be separated: an odometer is a successor/addition map, rather than this random fresh-digit transition ([Fisher, dynamical-systems notes](https://www.ime.usp.br/~afisher/ps/notes20230808.pdf)). A homeomorphism of underlying Cantor spaces does not identify their dynamical systems.

### The right deterministic object

For a deterministic map \(F:X\to X\) and a finite observation \(q:X\to Y\), an autonomous deterministic quotient exists exactly when
\[
q(x)=q(x')\quad\Longrightarrow\quad q(Fx)=q(Fx').
\]
Equivalently, \(qF=\bar Fq\) for some \(\bar F\). Applying strong lumpability to the Dirac transition kernel \(x\mapsto\delta_{F(x)}\) gives this same condition. Ordinary finite windows fail it; introducing a Markov partition does not automatically make it true.

There are two honest formalization choices:

- **Deterministic semantics:** formalize generalized-shift configurations, rewriting and head-motion rules, and an explicit simulation relation with `TM0`. Keep the necessary infinite tape, or a controlled/skew-product state carrying the symbols that enter the window. The existing `tail_shiftIn` law is a useful controlled-input identity, not a replacement for those semantics.
- **Measure-dependent observations:** choose an invariant measure and prove that the observed symbolic process is Markov under that measure, including the required conditional-independence statement. This is a statement about distributions, not a faithful pointwise simulator for every machine input.

Moore’s generalized shifts have the form \(\Phi(a)=\sigma^{F(a)}(a\bar\oplus G(a))\), where a finite window controls both a finite rewrite and a variable shift; his Theorem 7 constructs the TM simulation explicitly ([Moore, Generalized shifts](https://sites.santafe.edu/~moore/nonlinearity-gs.pdf)). The fluid work uses generalized-shift encodings to obtain Turing completeness ([Cardona–Miranda–Peralta-Salas–Presas](https://pmc.ncbi.nlm.nih.gov/articles/PMC8126859/)). A finite-state or sofic presentation, without an encoding and a proved relation between halting and a dynamical event, supplies no such conclusion.

Nor is a finite Markov partition a generic repair: Moore exhibits an observation language that is not a subshift of finite type, regular, or context-free, in his Example 1 ([Moore](https://sites.santafe.edu/~moore/nonlinearity-gs.pdf)). That is an example-specific obstruction to a blanket finite-state coding proposal, not an impossibility theorem about every conceivable symbolic realization.

This finding does **not** erase the separate computation result in `HaltingCompiler`. That module explicitly connects Mathlib `TM0` halting with the compiled curvature predicate. The unsupported step is transferring its computational meaning, or Moore’s, to the Bernoulli tower.

## Statistical attachment: promising, with a closure theorem still required

### Verdict

**A rigorous statistical bridge is available as a research direction, but invariant measure does not make all finite-state SGC tools apply natively.** A fixed Galerkin system is finite-dimensional, not finite-state; its invariant measure lives on a continuous phase space. A finite partition, sampling interval, observable norm, and approximation theorem remain necessary.

Determining modes are a related but different object: the cited three-dimensional determining-wavenumber results concern synchronization or identification of solutions from sufficiently many low modes over time, with solution-dependent cutoffs, not an exact instantaneous autonomous quotient or a minimal finite-time prediction resolution ([Cheskidov–Dai–Kavlie](https://arxiv.org/pdf/1507.05908); [Cheskidov–Dai](https://arxiv.org/pdf/1510.00379)). It is reasonable to use them as comparison targets; it is not correct to identify their number with an SGC validity resolution by definition.

For a precise contrast, the two-dimensional Foias–Prodi property says asymptotic agreement of the low modes and forcings of two solutions implies asymptotic agreement of the full solutions ([Determining Modes, Synchronization, and Intertwinement](https://ar5iv.labs.arxiv.org/html/2408.01064)). Cheskidov–Dai–Kavlie’s Theorem 1.1 assumes low-mode equality for all positive times to conclude synchronization, while Theorem 1.2 assumes equality over the whole past on the weak attractor to identify the trajectories ([Cheskidov–Dai–Kavlie](https://arxiv.org/pdf/1507.05908)). Those temporal quantifiers are the missing content in an attempted instantaneous-resolution interpretation.

### A measure produces a transition matrix, not necessarily a Markov observation process

Here is an explicit construction and its obstruction. Let \(S_t\) be a measurable solution evolution preserving a probability measure \(\mu\), choose cells \(A_1,\ldots,A_k\) with positive \(\mu\)-mass, and fix a sampling time \(\tau\). Define

\[
\pi_i=\mu(A_i),\qquad
K_\tau(i,j)=
\frac{\mu(A_i\cap S_\tau^{-1}A_j)}{\mu(A_i)}.
\]

Summing over \(j\) proves row-stochasticity; summing \(\pi_iK_\tau(i,j)\) over \(i\) and using invariance proves \(\pi K_\tau=\pi\). These are elementary measure identities. They do **not** prove that observations at several times are Markov, or that \(K_{m\tau}=K_\tau^m\).

The simplest counterexample needs no PDE. Take the deterministic four-cycle \(0\to1\to2\to3\to0\), its uniform invariant measure, and the cells \(A=\{0,1\}\), \(B=\{2,3\}\). Then

\[
K_1=\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix},
\qquad
K_2=\begin{pmatrix}0&1\\1&0\end{pmatrix}
\ne K_1^2.
\]

Thus even a finite deterministic system with an exactly known stationary measure does not acquire an autonomous coarse Markov law simply by averaging one-step transitions. Repeatedly using \(K_1\) discards information about the hidden position within each cell.

This has established methodological relatives: Ulam-type finite-state approximations of transfer operators require approximation estimates and do not enjoy unrestricted invariant-measure convergence ([Galatolo–Nisoli](https://arxiv.org/html/1109.2342v5)). Conditional-expectation reduction through Mori–Zwanzig retains a non-Markovian memory term rather than simply producing a closed drift equation ([Chorin–Hald–Kupferman](https://www.pnas.org/doi/pdf/10.1073/pnas.97.7.2968)). The four-cycle calculation above proves the obstruction directly without importing either framework’s additional hypotheses.

### A concrete statistical horizon theorem

The following is a mathematical derivation proposed for formalization, not a theorem already present in the audited tree. On \(H=L^2(\mu)\), let

\[
U\phi=\phi\circ S_\tau,\qquad
\Pi=\mathbb E_\mu[\,\cdot\mid A_1,\ldots,A_k],\qquad
A=\Pi U\Pi,\qquad
\delta=\|(I-\Pi)U\Pi\|_{H\to H}.
\]

Invariance makes \(U\) an isometry, and \(\Pi\) is an orthogonal projection, so \(\|U\|,\|\Pi\|,\|A\|\le1\). For \(E_m=U^m\Pi-A^m\Pi\), the exact recursion is
\[
E_{m+1}=UE_m+(U-A)A^m\Pi.
\]
Since \(A^m\Pi\) takes values in the range of \(\Pi\), induction gives
\[
\|U^m\Pi-A^m\Pi\|\le m\delta,
\qquad
\|\Pi U^m\Pi-A^m\Pi\|\le m\delta.
\]

The second inequality is a precise statistical forecast statement: conditional \(m\)-step predictions differ from iterating the one-step coarse predictor by at most \(m\delta\) for unit-\(L^2\) observables. Physical time is \(m\tau\); the sufficient tolerance condition is \(m\delta\le\eta\). This is the same contraction-and-telescoping mechanism as Kernel Horizon, extended to the specified probability space, rather than a new regularity principle.

Two qualifications matter. First, the vector mean of a residual can cancel; for the conditional-prediction residual \((I-\Pi)U\phi\), its mean is identically zero. Use a mean-square, absolute, or operator-norm quantity, not the mean vector; the fluid residual \(R_N\) is a different object and its mean is not asserted to vanish.

Second, \(\delta=0\) here is stronger than “the observations happen to be Markov in stationarity.” For a deterministic underlying evolution and a finite partition, it makes the next cell a deterministic function of the current cell almost surely; positive stationary cell weights then force that finite map to be a permutation. An i.i.d.-input window process may have exact Markov statistics without this statewise deterministic-factor property. This operator bound is therefore sufficient, potentially conservative, and not a characterization of every statistical closure.

### Dissipation does not remove the stationarity obstruction

In the unforced, mean-zero periodic viscous Galerkin setting, the energy estimate gives exponential decay to zero ([Morosi–Pizzocchero, Lemma 6.4](https://arxiv.org/html/1104.3832v1)). Consequently the global attractor is \(\{0\}\), and its only invariant probability measure is \(\delta_0\): this follows directly from that decay. A nontrivial stationary cascade requires an explicitly specified energy input or a different setting; “\(\nu>0\)” alone does not supply it.

For any invariant probability measure and integrable observable \(V\),
\[
\int V(S_t x)\,d\mu(x)=\int V(x)\,d\mu(x).
\]
If also \(V(S_t x)\le V(x)\) almost surely, equality of the integrals forces equality almost surely for each fixed \(t\). Thus a strictly decreasing integrable Lyapunov observable cannot be nontrivial on stationary typical trajectories. This obstruction survives viscosity: stationarity replaces time reversal as the relevant restriction.

There is nevertheless a useful finite-state monotone. For a stochastic matrix with stationary law \(\pi\), the log-sum inequality yields
\[
D_{\mathrm{KL}}(\rho K\|\pi)\le D_{\mathrm{KL}}(\rho\|\pi).
\]
For completeness, with positive \(\pi\), the elementary proof is to apply log-sum separately to each output column:
\[
\sum_j(\rho K)_j\log\frac{(\rho K)_j}{(\pi K)_j}
\le \sum_{i,j}\rho_iK_{ij}\log\frac{\rho_i}{\pi_i}
=D_{\mathrm{KL}}(\rho\|\pi).
\]
This is relaxation of a **nonstationary distribution** toward an invariant reference, not evolution of the invariant measure itself. Strict or quantitative decay requires further assumptions; in particular a permutation chain gives equality. For an invertible measure-preserving fine flow, change of variables similarly preserves the relative entropy of transported densities.

Relative entropy also contracts when distributions are pushed through a coarsening map. That orders information loss under the chosen observation map, not physical energy flux across Fourier scales, and supplies no regularity-versus-collapse threshold. Curvature, entropy production, and mixing can be worthwhile SGC observables without becoming singularity detectors.

There is a further curvature obstruction worth making explicit. The deterministic Galerkin evolution has phase-space generator \(\mathcal L\phi=F_M\cdot\nabla\phi\), even when its physical velocity equation includes viscosity; the Leibniz rule therefore gives
\[
\Gamma(\phi)=\tfrac12\bigl[\mathcal L(\phi^2)-2\phi\mathcal L\phi\bigr]=0.
\]
Physical-space viscosity is not a diffusion operator on Galerkin coefficient space. A nondegenerate Markov carré-du-champ would belong to a finite stochastic surrogate or to an explicitly noise-driven model, and its relationship to the original fluid must be proved.

The first pilot should therefore keep the Galerkin cutoff \(M\) fixed, specify autonomous forcing and an invariant measure, and separate Fourier resolution from the finite partition used for statistical observation. A two-dimensional setting is the safer continuum extension. For three-dimensional weak solutions, the stationary-statistical framework of Foias–Rosa–Temam uses generalized invariant objects and translation-invariant trajectory measures rather than assuming a unique strong phase-space semigroup; its energy condition is an inequality ([Foias–Rosa–Temam](https://www.numdam.org/item/10.1016/j.crma.2009.12.018.pdf)).

Merely taking \(M\to\infty\) does not discharge those obligations. The chosen invariant measure may also be nonunique, and a bound holding only almost surely or in mean cannot exclude exceptional trajectories on a null set. Those are reasons to specify the statistical goal precisely, not reasons to abandon statistical solutions.

Assuming an invariant measure also does not supply an algorithm for its cell probabilities. A sampled transition matrix needs an estimation-error guarantee in addition to the dynamical closure bound; these should remain separate terms in any proposed statistical certificate.

### Not every existing SGC theorem requires stationarity

The premise “every SGC theorem is \(\pi\)-weighted with a stationary measure” is incorrect for the inspected tree. `AbstractBKM` and `ResidualHorizon` have neither \(\pi\) nor stationarity hypotheses; `KernelHorizon.kernel_closure_error_le` requires positive reference weights and a stochastic matrix, but not stationarity, and uses an \(L^\infty\) operator norm. Its own scope comment says the bridge to the \(\pi\)-weighted norm remains planned.

Accordingly, a statistical direction is a choice based on the desired observable and theorem, not a consequence forced by all existing APIs. The trajectory and statistical branches may coexist, provided their residuals and guarantees are not conflated.

## Additional sentences requiring correction

This table concerns the pinned revision, including new text not covered merely by retaining the old conjecture for historical purposes. The explicitly marked original-text archive in Section 6.2 is not treated as a live claim.

| Location | Current wording or claim | Required correction |
|---|---|---|
| Theorem 2.5, paper lines 159–164 | “Moore’s shift is renormalization-transparent”; shift on `A^Z` identified with `PathSpace` | Replace with exact lumpability of uniform fresh-symbol finite-word kernels; the implemented path space is one-sided |
| Paper Section 3.2, line 204 | “The Moore leg is the one SGC has actually formalized” | The Bernoulli tower is formalized; a Moore/TM simulation bridge is not |
| `CantorShiftTower.lean:22–49` | `shiftTower_defect_zero` identified with “unbounded faithful simulation (Turing completeness)” | Remove this implication; retain an explicitly unproved research dictionary |
| Paper line 337; `ResidualHorizon.lean:27` | \(P_NB(u,u)-B(P_Nu,P_Nu)=P_N[B(u,u)-B(P_Nu,P_Nu)]\) | The left expression lacks the second output projection; use \(R_N=P_N[B(u,u)-B(P_Nu,P_Nu)]\) |
| Paper lines 413–415 | The residual “is” \(C_N(u)\) | With the stated \(B\) and NS vector-field convention it is \(-R_N\); the norm is unaffected |
| Paper lines 362–364 | BKM divergence forces unbounded re-entry at every fixed scale | Retract here too; this live bullet contradicts the later retraction |
| Paper lines 391–398; `ResidualHorizon.lean:49–52` | \(\|C_N\|\lesssim NE\), followed by resolution escape | Specify the norm; an individual Fourier-coefficient bound is \(O(NE)\), while the stated three-dimensional \(L^2\) estimate is \(O(N^{5/2}E)\); neither proves resolution escape |
| Paper lines 420–438 | \(N_\eta\) is “the determining wavenumber”; projected tracking fails for every tolerance | Different definitions and quantifiers; large \(L^2\) tolerance already defeats the proposed universal statement |
| `ResidualHorizon.lean:35–37,109–110` | Zero residual gives “infinite validity horizon” | Exact tracking on every interval where the existence and regularity hypotheses hold; not an existence theorem |
| New commission’s theorem count | “168 = {propext, Classical.choice, Quot.sound}” | 168 closures are contained in that base; 151 equal the full three-element set |
| Residual receipt and pinned source | Exact current-statement provenance | Regenerate: the receipt includes `hT : 0 ≤ T`, the pinned source does not |
| New commission’s stochastic description | “odometer / Bernoulli shift” | These are different dynamical systems; the implemented kernel is the uniform fresh-symbol shift |

The \(L^2\) residual bound in the table follows by summing the coefficient bound over \(O(N^3)\) retained modes and applying the same estimate to the projected nonlinear term. Constants depend on Fourier and torus normalization; no numerical physical-unit constant is certified here.

## Recommended decision

Keep “validity horizon” as a name for a **specified certified guarantee**, not an intrinsic phase boundary. The trajectory version should distinguish existence from accuracy and cite the a posteriori literature before any novelty language; the statistical version should specify the measure, observation, sampling time, and non-Markov closure error.

The next theoretical deliverable should be a short specification containing the two residual identities, the certificate-completeness quantifiers, and the statistical operator construction with the four-cycle regression test. If a formalization sprint is later authorized, the already accepted Fourier counterexample, fixed-cutoff bounds, cancellation identity, and inhomogeneous energy estimate remain a sound order. A statistical pilot can then be assessed on its own merits, without waiting for a continuum singularity theorem or defending the Bernoulli tower as a Turing machine.

The audit does not justify abandoning SGC’s finite-state theory. It justifies removing the unproved equivalences that were making the theory appear to answer a different question.
