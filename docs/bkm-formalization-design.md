# Beale–Kato–Majda in Lean 4 — design note (2026-08-26)

Target: the BKM continuation criterion — a smooth Euler/NS solution on
[0,T*) extends past T* iff the vorticity budget INT_0^{T*} ||w(t)||_Linf dt
is finite. Epistemic frame: BKM compresses blow-up into divergence of one
scalar budget; it is the continuum twin of the SGC validity-horizon
functionals, and the natural verification spine for Tao-style
computational-blow-up programs (Miranda/Moore undecidability lives at the
trajectory level; regularity-independence is conjecture, not theorem).

## Layer ladder

L0 (provable NOW, target module SGC/Bridge/AbstractBKM.lean):
  Abstract quadratic ODE u' = B(u,u) + nu*A u in a finite-dim/Banach space
  with a budget functional W(t) >= 0 satisfying d||u||/dt <= C*W*||u||:
  - gronwall_budget: ||u(t)|| <= ||u_0|| * exp(C * INT_0^t W)
  - continuation: INT W finite on [0,T) + Picard-Lindelof => extension
  - bkm_dichotomy (finite-dim): maximal T* < inf => INT_0^{T*} W = inf
  Mathlib inventory: gronwallBound + norm_le_gronwallBound_of_norm_deriv_
  right_le (Analysis.ODE.Gronwall), Picard-Lindelof (Analysis.ODE.
  PicardLindelof). Risk: maximal-solution API is thin; may need our own
  small maximal-interval development.

L1 (months): Fourier H^s on T^3 as weighted l^2 (Mathlib Fourier series),
  Galerkin-truncated NS as L0 instance, budget = ||w_N||_inf, constants
  uniform in N. Delivers: BKM for every Galerkin approximation, kernel-
  proven; the discrete-fluid track (DiscreteFluidDynamics) gets its
  continuum-facing budget functional.

L2 (community-scale, YEARS; the honest wall): Biot-Savart on R^3/T^3,
  Calderon-Zygmund boundedness (absent from Mathlib), and the log
  interpolation ||grad u||_inf <~ ||w||_inf (1 + log+(||u||_{H^s}/||w||_inf)).
  Gagliardo-Nirenberg-Sobolev exists (Analysis.FunctionalSpaces.
  SobolevInequality) as the only current foothold.

L3: Kato local existence (mild solutions/heat semigroup) + L2 + double-
  exponential Gronwall + continuation = full BKM.

## Ecosystem facts (2026-08, verified)

- Clay STATEMENT formalizations exist: lean-dojo/LeanMillenniumPrizeProblems
  (Fefferman A-D; note its first version was satisfiable VACUOUSLY via a
  degenerate domain and had to be repaired — the same degenerate-parameter
  disease our satisfiability-first sweep hunts) and a DeepMind
  formal-conjectures PR (#1457).
- navier-stokes.dev: ~190-theorem Lean 4 conditional-regularity reduction
  over 12 NAMED AXIOMS (incl. Picard-Lindelof and Gronwall, which Mathlib
  actually has — partial discharge opportunity). Frontier style today =
  verified reductions, not proofs.
- BKM itself: formalized nowhere; L2 is the reason.

## SGC angle

1. L0 is a horizon theorem of exactly our proven shape (Kernel Horizon:
   error <= n*||C||; uniform: <= ||C||/(1-alpha); BKM-L0: growth <=
   exp(C*INT W)). Budget-finiteness = validity continuation is the
   program's signature move, now aimed at the continuum.
2. Undecidability split kept honest: BKM can be exactly true while the
   budget's divergence is algorithmically undecidable from initial data —
   the eps = 0 / eps > 0 split of SGC appearing inside the Clay problem.
3. Analogy discipline: horizon-functional correspondence is FRAMING until
   an L1 theorem links a discrete defect to a Galerkin vorticity budget.

## Recommended first sprint (when chosen)

AbstractBKM.lean: finite-dimensional L0 ladder (gronwall_budget,
budget_finite_implies_bounded, bkm_dichotomy for quadratic ODEs), audit-
gated, zero axioms. Then evaluate Mathlib's maximal-solution gap before
promising L1.
