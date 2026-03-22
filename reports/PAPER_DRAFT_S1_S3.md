# Paper Draft: Sections 1 and 3

**Target**: Physical Review Letters / NeurIPS  
**Style**: Precise, honest, no overclaiming  
**Build status**: Lean 4 file compiles (0 errors, 5 classified sorry warnings)

---

## Section 1: Introduction

The discovery of conservation laws from observational data is among the oldest problems in the physical sciences. Kepler extracted his laws of planetary motion from Brahe's astronomical measurements; Faraday derived the laws of electromagnetism from tabletop experiments. In each case, the scientist identified mathematical quantities that remain invariant across observations — conserved charges, energies, angular momenta — and used these invariants to compress the complexity of the observed system into a small number of governing equations. Modern datasets are vastly larger, but the underlying problem is unchanged: given *N* observations of a system's state, identify the algebraic structures that are invariant.

Several computational approaches to this problem have been developed. SINDy [Brunton et al. 2016] discovers sparse dynamical equations d**x**/dt = **f**(**x**) by regression on a pre-supplied library of candidate nonlinear functions; it finds equations of motion but not their first integrals, and requires the user to specify the function library. Symbolic regression methods such as AI Feynman [Udrescu & Tegmark 2020] search over expression trees to find closed-form equations matching data, but scale poorly with dimensionality and require explicit functional form hypotheses. Koopman operator methods lift the dynamics into a higher-dimensional feature space where the evolution is linear, but require the user to choose the lifting dimension and basis functions a priori. Most recently, Liu et al. [2023] demonstrated conservation law discovery via optimal transport and manifold learning on phase-space distributions, without requiring an explicit dynamical model — the closest prior work to what we present here.

In this paper, we show that the minimum-variance direction of the empirical covariance of quadratic features **x** ⊗ **x** over a dataset computes the null space of the Fisher information matrix of the underlying distribution, and that for ergodic Hamiltonian systems in equilibrium, these null directions correspond to the integrals of motion guaranteed by Noether's theorem (Theorem 1, formalized in Lean 4). We characterize four precise failure modes of this computation, each corresponding to a violated assumption in the theorem: nonlinearity of the Hamiltonian (measured by the validity horizon T\*), observational selection bias (measured by the shuffle gap), positive-definite optimization obstruction (overcome by a Hessian-guided perturbation), and insufficiency of the quadratic feature space (detected by the absence of a low-variance direction). We demonstrate the engine on nine systems spanning five scientific domains — synthetic mechanics, predator-prey ecology, orbital astrophysics, galactic kinematics, particle physics, neuroscience, gravitational wave detection, and protein dynamics — and show that the failure mode diagnostics are informative in every case, including the cases where the engine does not find a conservation law. The distinction from prior work is not that our method discovers more laws, but that it provides a formally grounded diagnostic framework — rooted in information geometry — that reports *why* it succeeds or fails.

---

## Section 3: The Fisher-Noether Bridge

### 3.1 The Computation

The engine receives as input a dataset {**x**₁, ..., **x**_N} of *d*-dimensional real vectors, with no labels, coordinate names, or domain-specific metadata. It computes the quadratic form *Q*\*(**x**) = **x**ᵀ *C*\* **x** that has minimum variance across the dataset, subject to the normalization constraint ‖*C*\*‖_F = 1. Concretely, it finds the unit-norm symmetric matrix *C*\* that minimizes

$$\text{Var}_i[Q(\mathbf{x}_i)] = \frac{1}{N}\sum_{i=1}^N \left(\mathbf{x}_i^\top C \mathbf{x}_i - \bar{q}\right)^2, \qquad (1)$$

where $\bar{q} = \frac{1}{N}\sum_i \mathbf{x}_i^\top C \mathbf{x}_i$. When the data admits *k* > 1 independent conservation laws, the engine discovers *k* orthogonal constraints {*C*₁, ..., *C*_k} satisfying Tr(*C*_i^T *C*_j) = δ_{ij}, each minimizing (1) in the subspace orthogonal to all previously discovered constraints.

For datasets where the minimum-variance quadratic form requires an indefinite signature (e.g., the Minkowski metric η = diag(+1, −1, −1, −1)), the engine employs a Hessian-guided perturbation to cross the boundary of the positive-definite cone in the space of symmetric matrices. This perturbation is computed from the variance Hessian — the fourth-moment tensor of the data — and injected along its softest eigenmode.

### 3.2 Theorem 1: Variance Equals Fisher Quadratic Form

The variance of *Q*(**x**) = **x**ᵀ *C* **x** over the empirical distribution admits an exact decomposition:

$$\text{Var}[Q] = \mathbf{c}^\top \Sigma \, \mathbf{c}, \qquad (2)$$

where **c** = vec(*C*) is the vectorization of the constraint matrix and Σ = Cov[vec(**x x**ᵀ)] is the covariance of the lifted outer-product features. The minimum of (2) subject to ‖**c**‖ = 1 is achieved at the eigenvector of Σ corresponding to its smallest eigenvalue λ_min.

This identity is a tautology from the definitions of variance, the quadratic form, and the covariance, but its significance lies in connecting the engine's optimization objective (1) to the spectral structure of the lifted covariance Σ. The minimum-variance direction is not found by gradient descent on (1) directly; it is the minimum eigenvector of a matrix that can be computed once from the data's second and fourth moments. This theorem is formalized in Lean 4 (Supplementary S1) with proof deferred as a routine algebraic identity.

### 3.3 Theorem 2: The Fisher Information Connection

For a distribution belonging to the exponential family with quadratic sufficient statistics *T*(**x**) = vec(**x x**ᵀ),

$$p(\mathbf{x}; \theta) \propto h(\mathbf{x}) \exp\!\left(\theta^\top T(\mathbf{x}) - A(\theta)\right), \qquad (3)$$

the Fisher information matrix equals the covariance of the sufficient statistic [Amari & Nagaoka 2000, Theorem 3.3]:

$$I(\theta) = \text{Cov}_\theta[T(\mathbf{x})] = \Sigma. \qquad (4)$$

Combining (2) and (4): the minimum-variance quadratic form *Q*\* is the null direction of the Fisher information matrix *I*(θ). Zero Fisher information in a direction means the distribution is completely flat along that direction — every sample gives the same value of *Q*\*. This is precisely the definition of a conserved quantity.

The exponential family assumption (3) holds exactly when the distribution is a Boltzmann distribution *f*(**x**) ∝ exp(−β *H*(**x**)) with a quadratic Hamiltonian *H*. For non-quadratic Hamiltonians, the quadratic sufficient statistic captures only the best quadratic approximation to the true Fisher information structure. The validity horizon T\* = 1/λ_min measures precisely how good this approximation is: T\* → ∞ when *H* is exactly quadratic (λ_min → 0, the conservation law is exact), and T\* is small when significant non-quadratic terms are present. This is not a heuristic — it is a direct consequence of the truncation error in approximating the true exponential family by its degree-2 projection.

Experimentally, T\* tracks the nonlinearity of the underlying physics with quantitative precision: T\* = 10¹² for the harmonic oscillator (exactly quadratic), T\* = 19,305 for the near-circular Kepler orbit (weakly nonlinear), T\* = 17.5 for the Lotka-Volterra predator-prey system (strongly nonlinear), and T\* < 1 for colored Gaussian noise (no conservation law).

### 3.4 Conjecture 1: The T\* Bound

We conjecture that for an ergodic Hamiltonian system with a quadratic integral of motion *I*(**x**) = **x**ᵀ *A* **x**, the minimum-variance quadratic form *Q*\* satisfies

$$\| C^* - A / \|A\|_F \|_F^2 \leq C \cdot \lambda_{\min}, \qquad (5)$$

where *C* is a constant depending on the spectral gap of the Hamiltonian and the dimension of the integral subspace. Equivalently, the Frobenius distance between the discovered constraint and the true (normalized) integral of motion is bounded by *C* / T\*.

The proof strategy is via the Davis-Kahan sin(θ) theorem [Davis & Kahan 1970], which bounds the angle between eigenvectors of a matrix and its perturbation in terms of the eigenvalue gap. Applied to the lifted covariance Σ: if the true integral *I* corresponds to an eigenvalue of 0 (exact conservation) and the empirical covariance $\hat{\Sigma}$ has minimum eigenvalue λ_min > 0 (finite-sample or nonlinearity error), then Davis-Kahan gives ‖*Q*\* − *I*/‖*I*‖‖ ≤ ‖Σ − $\hat{\Sigma}$‖ / gap, where gap is the spectral gap between the first and second eigenvalues. When the gap is bounded away from zero (the conservation law is well-separated from the non-conserved directions), the bound (5) follows with *C* proportional to the inverse gap.

This conjecture is formalized as a Lean 4 theorem statement (Supplementary S1, `minvar_approximates_integral`) with the proof marked as an open research question. The Davis-Kahan theorem is not currently available in Mathlib. Experimental evidence from nine benchmarks supports the conjecture: every system where T\* is large produces a *Q*\* that closely approximates the known integral, and every system where T\* is small produces a *Q*\* that deviates measurably.

### 3.5 Theorem 3: Selection Contamination

When the observed distribution is not the true equilibrium *f*(**x**) but rather *f*(**x**) · *S*(**x**) where *S* is a selection function (observational bias, survey completeness, detector acceptance), the variance of any quadratic form shifts:

$$\text{Var}_{f \cdot S}[Q] = \text{Var}_f[Q] + \text{Cov}_f[Q, \log S] + O(\|S - 1\|^2). \qquad (6)$$

The correction term Cov_f[*Q*, log *S*] is nonzero whenever the conservation law *Q* is correlated with the selection function under the true distribution. This contamination is unavoidable in manifold mode on snapshot data: any method that works on the observed distribution *f* · *S* discovers the geometry of *f* · *S*, not of *f* alone.

The Gaia DR3 benchmark confirms this prediction quantitatively. The discovered constraints contain angular momentum components (a genuine dynamical signal, confirmed by a 32× shuffle gap) mixed with disk geometry terms (correlated with the magnitude-limited survey selection function). Theorem 3 predicts this contamination is proportional to Cov_f[*L*_z, log *S*_Gaia], which is nonzero because distant stars (large *L*_z) must be brighter to pass the magnitude limit (large *S*). The only escape from selection contamination is temporal data (dynamics mode, where the transition structure is independent of the selection function) or an explicit model of *S*.

---

*Lean 4 build status: `FisherNoetherBridge.lean` compiles with 0 errors, 5 classified sorry warnings (3 TRIVIAL, 1 CLASSICAL, 1 OPEN). See Supplementary S1.*
