/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/

-- Foundation: The L²(π) Inner Product Structure
import SGC.Axioms.Geometry
import SGC.Axioms.GeometryGeneral
import SGC.Axioms.WeightedSpace

-- Spectral Pillar: Heat Kernel, Sector Envelope, and Core Stability Theorem
import SGC.Spectral.Envelope
import SGC.Spectral.Defs
import SGC.Spectral.Diagonal
import SGC.Spectral.Core.Assumptions
import SGC.Spectral.Core.Projector
import SGC.Spectral.Envelope.ODE
import SGC.Spectral.Envelope.Sector

-- Renormalization Pillar: Spectral Gap Monotonicity
import SGC.Renormalization.Lumpability

-- Approximate Renormalization: Trajectory bounds for leakage defects
import SGC.Renormalization.Approximate

-- Topology Pillar: Geometric Markov Blankets
import SGC.Topology.Blanket

-- Symbolic / p-adic Layer (Cantor tier): uniformly p-ary path space, the base-p digit
-- encoding (Fin n → Fin p) ≃ ZMod (pⁿ), and (TODO) the homeomorphism to ℤ_[p]
import SGC.Topology.PadicPathSpace

-- Thermodynamics Pillar: Stochastic Thermodynamics of Surprise
import SGC.Thermodynamics.DoobMeyer
import SGC.Thermodynamics.EntropyProduction
import SGC.Thermodynamics.FluxDecomposition

-- Variational Pillar: Principle of Least Action
import SGC.Variational.LeastAction

-- Complexity Relativity: complexity is observer-relative, not intrinsic to L
import SGC.ComplexityRelativity

-- Bridge Pillar: Continuum Limits and Quantum Correspondence
import SGC.Bridge.Discretization
import SGC.Bridge.Quantum
import SGC.Bridge.CanonicalWavelet
import SGC.Bridge.CoherenceObstruction
import SGC.Bridge.Consolidation
import SGC.Bridge.GeometricClosure
import SGC.Bridge.Recovery

-- Observables Pillar: Complexity Measures and Thermodynamic Bounds
import SGC.Observables.ThermodynamicBounds
import SGC.Observables.TopologicalPersistence
import SGC.Observables.ValidityHorizon

-- Examples: Validation and Smoke Tests
import SGC.Examples.ThreeStateCycle

-- Information Geometry: Tsallis Statistics
import SGC.InformationGeometry.TsallisStatistics

-- Dynamics: Escort Conductance and Boundary Mechanisms
import SGC.Dynamics.EscortConductance

-- Symbiotic Architecture: Continual Learning via Autonomous Growth
import SGC.Symbiosis

-- Spin-Glass Correspondence: Frustration, Gauge Theory, and Polarity Learning
import SGC.SpinGlass

-- ═══════════════════════════════════════════════════════════════════════════
-- SGC Extensions: The Constructive Physics Layer
-- ═══════════════════════════════════════════════════════════════════════════

-- Information Bridge: Shannon Entropy ↔ Geometric Orthogonality
import SGC.Information.Gaussian
import SGC.Information.Equivalence
import SGC.Information.RateOfConsolidation

-- Continuum Bridge: Graphs → Manifolds
import SGC.Geometry.Manifold.Laplacian
import SGC.Geometry.Manifold.Convergence

-- Discrete Curvature: Yamabe Flow and Consolidation
import SGC.Geometry.DiscreteCurvature
import SGC.Geometry.CurvatureBridge

-- ═══════════════════════════════════════════════════════════════════════════
-- Phase 5: Topological Evolution (Level 2)
-- ═══════════════════════════════════════════════════════════════════════════

-- Evolution: Ricci Flow with Surgery
import SGC.Evolution.FormanRicci
import SGC.Evolution.Surgery
import SGC.Evolution.Conservation
-- Stage 4: The Dynamics of Evolution (hybrid system lifecycle)
import SGC.Evolution.Dynamics

-- ═══════════════════════════════════════════════════════════════════════════
-- Phase 6: Thermodynamics of Evolution (The Cost of Change)
-- ═══════════════════════════════════════════════════════════════════════════

-- Landauer's Principle: Surgery has thermodynamic cost
import SGC.Thermodynamics.Evolution

-- ═══════════════════════════════════════════════════════════════════════════
-- Phase 7: Discrete Conformal Geometry (The Geometric Engine)
-- ═══════════════════════════════════════════════════════════════════════════

-- Constructive geometry via Koebe-Andreev-Thurston theorem
import SGC.Geometry.Simplicial
import SGC.Geometry.Conformal
import SGC.Geometry.Yamabe

-- ═══════════════════════════════════════════════════════════════════════════
-- Phase 8: The Consolidation Layer (Functional Blankets, Grokking, Renner Bridge)
-- Wired into the gate 2026-06-09: the default build must SEE this layer's
-- theorems and its remaining debt (sorry warnings are visible by design).
-- ═══════════════════════════════════════════════════════════════════════════

-- Functional Blanket: π-weighted ANOVA, functional defect, class separation
import SGC.FunctionalBlanket

-- Adiabatic Invariants: constrained updates, catastrophic forgetting prevention
import SGC.ContinualLearning.AdiabaticInvariant

-- Renner Bridge: prediction error ↔ dissipation (kernel-coupled axioms +
-- kernel-proven ground case collapsed_states_imply_exact_lumpability)
import SGC.Bridge.RennerSGC

-- Information Gradient Law: Fisher metric, natural gradient, transition condition
import SGC.InformationGeometry.InformationGradientLaw

-- Kramers Escape: barrier crossing for grokking dynamics (open sorries, exposed)
import SGC.InformationGeometry.KramersEscape

-- Multi-level RG: quotient generators, Dirichlet gap composition
import SGC.Renormalization.QuotientGenerator

-- The Grokking Rosetta Stone: unified consolidation exports
import SGC.Grokking

-- Emergence Equivalence: the four-way characterization of emergence (P* is
-- simultaneously information-optimal, thermodynamically efficient, and
-- variationally stable) + the Persistence Theorem (to_persist_is_to_predict).
-- Proven sorry-free 2026-06; wired 2026-06-09 (was invisible to the gate).
import SGC.EmergenceEquivalence

-- Cellular Sheaves: local stalks, restriction maps, sheaf consistency —
-- the discrete top-down constraint structure (compositional gluing)
import SGC.Structure.CellularSheaf

-- Local-to-Global Computation: unique global sections on computation DAGs,
-- the proved Sheaf Assembly theorem, the Sheaf-Connector impossibility
-- theorem (diffusion ≠ composition), defect propagation, and grokking as
-- the zero-defect transition (proved 2026-07-25, Bosca–Ghrist bridge)
import SGC.Structure.LocalToGlobal

-- Continual Compositional Assembly: expression grammar as native sheaf,
-- certified local ops => correct evaluation of ALL composite expressions
-- (zero-shot), safe extension => formal no-forgetting theorem, legacy
-- (x+y)z machine embeds invariantly into the grammar (2026-07-25)
import SGC.Structure.ContinualComposition

-- Certified Lifelong Substitution: safe extensions form a category (refl,
-- comp, finite chains), lifelong no-forgetting, substitution/grafting
-- theorem, and the capstone: Certified + SafeExtension* + Substitution
-- => Preservation + ExactComposition (2026-07-25)
import SGC.Structure.LifelongSubstitution

-- Recursive Error Budget: B(leaf)=0, B(op(e..)) = delta_op + sum L_i B(e_i)
-- with data-dependent Lipschitz constants; induction theorem
-- |evalLearned e - evalRing e| <= B(e) at arbitrary depth (generalizes T4),
-- sheaf-level bound via section uniqueness, and grokking as budget
-- collapse: zero local defects => exact global semantics (2026-07-26)
import SGC.Structure.ErrorBudget

-- Certified Consolidation: temporal system with plastic active state and
-- protected memory; consolidation = safe extension; lifelong memory
-- preservation + exact/bounded composition at every time; concrete witness
-- that such a system is possible (2026-07-26)
import SGC.Structure.TemporalConsolidation

-- Adaptive Coherence Descent ladder: discrete Lyapunov layer (energy
-- antitone + convergence), quantified residual descent (R(A_t) -> 0),
-- attention gate (descent by construction for ANY policy), and the Safe
-- Adaptive Consolidation capstone: gated attention + safe consolidation
-- => coherence descent + lifelong no forgetting (2026-07-26)
import SGC.Structure.CoherenceDynamics
import SGC.Structure.ResidualDescent
import SGC.Structure.AttentionGate
import SGC.Structure.TemporalCoherence

-- Fisher-Noether Bridge: min-variance quadratic forms = null Fisher directions
-- (Link 1 proven 2026-06; Bridge composed 2026-06-10 after deleting the
-- inconsistent expfam axiom). 2 sorries visible by design:
-- 1 deferred-standard (Rayleigh) + 1 open research (Davis-Kahan).
import SGC.InformationGeometry.FisherNoetherBridge

-- Defect Dynamics: Lyapunov staging for the learning-side defect.
-- 2026-06-10 hygiene pass: projected_update_zero_defect un-axiomatized,
-- two vacuous tautology-axioms + one false Pythagorean axiom DELETED,
-- honest IsLyapunovStable/IsExponentiallyAttracting vocabulary added.
-- Now axiom-free and sorry-free.
import SGC.InformationGeometry.DefectDynamics

-- Discrete Fluid-Computer Bridge: bridge lemmas B1-B6 of the Miranda program
-- (continuity equation, static-fluid equilibrium, cycle-space H¹ obstruction,
-- current-aggregation heredity, uniform-fiber h-principle lift, viscous horizon).
-- Kernel-proven, no new axioms (2026-06-10).
import SGC.Bridge.DiscreteFluidDynamics

-- Three-Phase SGC Classifier: discrete Chern-Hamilton phases (Crystal/Mixing/
-- Universal over KillingDefect x DirichletGap), coarse-generator bridge, and the
-- RG-monotone flow theorem (rg_flow_crystalward: consolidation is one-way toward
-- rigidity). Kernel-proven, no new axioms (2026-06-11).
import SGC.Bridge.PhaseClassifier

-- The Emergence Loophole: how computation escapes the crystal-ward flow.
-- Drive injection (crystal transparency: KillingDefect(L+D) = KillingDefect(D)
-- exactly on a detailed-balance substrate), no-spontaneous-universality
-- packaging, and the validity horizon T* ~ 1/epsilon (semigroup perturbation
-- bound proved from the exponential series in an abstract real Banach algebra).
-- Kernel-proven, no new axioms (2026-06-11).
import SGC.Bridge.ValidityHorizon

-- The Defect-Horizon Bridge: identifies ValidityHorizon's abstract leakage
-- ε = ‖B‖ with Approximate's concrete defect ‖(I−Π)LΠ‖_π via the weighted
-- operator algebra PiMat (π in the type, NormedRing/NormedAlgebra instances),
-- proves e^{t(L−D)}Π = e^{tL̄}Π (invariant-subspace exponentiation), and
-- derives the explicit trajectory bound defect_horizon_bound — superseding
-- the axioms HeatKernel_opNorm_bound and Horizontal_Duhamel_integral_bound
-- with computable exponential constants. Kernel-proven (2026-06-11).
import SGC.Bridge.DefectHorizonBridge

-- Axiom retirement (2026-07-05): kernel-clean re-proofs of trajectory_closure_bound,
-- vertical_error_bound, propagator_approximation_bound, spectral_stability_reversible,
-- NCD_uniform_error_bound, and PropagatorDiff_eq_proj_trajectory_diff (ex-axiom),
-- name-stable in SGC.Approximate. The axioms HeatKernel_opNorm_bound,
-- Duhamel_integral_bound, Horizontal_Duhamel_integral_bound are DELETED.
import SGC.Bridge.TrajectoryClosure

-- The Cantor Shift Tower (2026-07-07): Moore's symbolic dynamics as an exact
-- (ε = 0) strongly-lumpable SGC renormalization tower on cylinder truncations;
-- tower projections intertwine the true shift on PathSpace ≃ ℤ_[p] (Cantor set).
-- Closes the Moore leg of the fluid-computation triangle (Miranda ↔ Cantor ↔ SGC).
import SGC.Bridge.CantorShiftTower

-- Exotic Pairs (2026-07-07): the discrete shadow of exotic ℝ⁴ — generator pairs
-- that are coarse-isomorphic (same quotient, both strongly lumpable, same coarse
-- model) yet fine-inequivalent (KillingDefect 0 vs > 0); the hidden handle's
-- circulation casts no coarse shadow. The coarse face never determines the fine
-- irreversibility invariant, as homeomorphism never determines smoothness in d=4.
import SGC.Bridge.ExoticPairs

-- Affinity Protection (2026-07-07): the conserved charge sealing the exotic phase —
-- the affinity charge (division-free Kolmogorov holonomy, a discrete Wilson loop)
-- vanishes on every cycle under detailed balance w.r.t. ANY positive measure; one
-- charged cycle forces KillingDefect > 0 for EVERY positive measure; charge-conserving
-- annealing can never reach criticality. The exotic lift's handle carries charge
-- (a+δ)³ − a³ > 0 for every base model, so the exotic pair lies in different
-- affinity classes: "homeomorphic but never diffeomorphic", now with a conserved
-- class datum witnessing the obstruction.
import SGC.Bridge.AffinityProtection

-- Schnakenberg Basis (2026-07-08): the realizability converse — every antisymmetric
-- charge assignment on the fundamental cycles of a star tree is realized by an
-- explicit conservative generator with nonnegative rates. Key linearization: pinning
-- star-tree edges to symmetric rate 1 collapses the polynomial Wilson loop to the
-- chord antisymmetry q x y − q y x (the star gauge abelianizes the holonomy). With
-- Phase E this completes the classification: affinity data is conserved (E) and free
-- (F) — the exact parameter space of the NESS landscape. Cycle space packaged as a
-- genuine Submodule; triangle currents proven to be 1-cycles.
import SGC.Bridge.SchnakenbergBasis

-- Schnakenberg Independence (2026-07-09, F2 part 1): the fundamental triangle
-- currents, indexed by ORDERED chords x < y (one representative per unordered
-- pair — triCurrent v₀ x y = −triCurrent v₀ y x), are linearly independent:
-- evaluation at each chord edge is a separating dual family (Kronecker delta
-- on ordered chords; the reversed match is killed by strictness).
import SGC.Bridge.SchnakenbergIndependence

-- Schnakenberg Span (2026-07-09, F2 completion): the chord currents SPAN the
-- cycle space — star edges follow from conservation, not counting: the defect
-- J − S is a cycle vanishing off-star, and divergence-freeness kills its star
-- edges. Packaged as Module.Basis (chordBasis); headline dimension count
-- 2·finrank(cycleSpace) = (n−1)(n−2), division-free via the swap involution.
-- The affinity data is conserved (E), free (F), and of exact dimension
-- (n−1)(n−2)/2 (F2): the parameter count of the NESS landscape — the first
-- Betti number of the complete graph, realized by star-tree fundamental cycles.
import SGC.Bridge.SchnakenbergSpan

-- Graph Heat Flow (2026-07-22, Phase 4 vertical slice): Dirichlet energy is
-- non-negative and dissipates under explicit-Euler steps within the CFL bound
-- h·maxDegree ≤ 1. Exact-real side of the heat-flow artifact contract; the
-- float64 companion receipt lives in the vault registry.
import SGC.Heat.GraphHeat

-- Curvature Undecidability (2026-08-02): deciding a GLOBAL Bakry-Émery bound
-- for a computable Markov generator is Π⁰₁-hard — equivalent to the complement
-- of the halting problem — already on the bi-infinite path with rates in {1,4}.
-- Two kernel-clean halves: an exact discrete Bochner identity making Γ₂ a sum
-- of three squared second differences (so the flat line is CD(0,∞)), and a
-- one-edge gadget whose explicit step-function witness gives Γ₂ = -1/4 < 0.
-- Fixed geometry, no marked point, no fluid dynamics: the Euler/Beltrami route
-- is not needed for the hardness half, and a spectral-gap transfer provably
-- does NOT follow (both branches have gap 0).
import SGC.Bridge.CurvatureUndecidability

-- Curvature Quotient (2026-08-02): Bakry-Emery curvature bounds DESCEND along
-- exactly lumpable quotients — CD(rho, inf) upstairs forces CD(rho, inf)
-- downstairs, same rho. The whole Gamma-calculus intertwines because lifting is
-- multiplicative as well as generator-intertwining (L_lift_eq), so Gamma and
-- Gamma_2 both commute with coarse-graining. Settles the question the research
-- foraging flagged as Contested and load-bearing. One-way only: renormalization
-- can only improve curvature, so coarse-graining is a sound one-sided
-- certificate for curvature VIOLATION and useless for verification.
import SGC.Renormalization.CurvatureQuotient

-- Halting Compiler (2026-08-09): the computability bridge that upgrades the
-- curvature gadget into a genuine Turing-machine theorem. Compiles Mathlib's
-- TM0 machines into exact-step Boolean markers (haltMarker, total and
-- structurally recursive), proves the at-most-once hypothesis as a THEOREM,
-- bridges the fuel-indexed simulation to Mathlib's PFun.fix evaluation
-- semantics, and concludes: CD0 (haltW (haltMarker M w)) <-> NOT (TM0.eval M
-- w).Dom. Deciding the global Bakry-Emery bound on the compiled family IS
-- deciding non-halting. Both poles inhabited by explicit machines.
import SGC.Bridge.HaltingCompiler

-- The Resolution Horizon (2026-08-09): halting fuel = cylinder depth =
-- curvature-defect location, as one kernel theorem cluster. The compiled
-- machine's halting history IS a point of the Cantor space (markerPath);
-- halting at fuel T is coordinate T of the depth-(T+1) truncation; below
-- that depth the marker path EQUALS the never-halting path (resolution
-- blindness, exact); and the compiled generator's Gamma_2 is pointwise >= 0
-- at every site whose four-edge stencil avoids T (localized Bochner,
-- stencil derived not assumed). Undecidable content is concentrated at one
-- resolution depth and one lattice edge — the same number T.
import SGC.Bridge.CantorHalting

-- The Discrete Operator-Strain Bridge (2026-08-09): NS-Table goal 1,
-- discrete-first. The exact Bochner-with-strain identity on the weighted
-- line: Gamma_2 = Hessian sum-of-squares + strain quadratic form on the
-- gradient (strainL/strainR = deviation of the rate field from local
-- flatness) — the discrete shadow of Gamma_2 = nu^2 |Hess f|^2 +
-- (nu Ric - S_u)(grad f, grad f). Zero strain => CD(0,inf); uniform drift
-- is strain-free (discrete constant vector field); ANY single-edge strain
-- s > 0 breaks CD(0,inf) witnessed by the identity function (the rate-4
-- gadget was the s = 3 point); total strain forms a dipole summing to
-- 8 s^2 >= 0 — the discrete precursor of trace-free incompressible strain.
-- All identities CAS-derived before formalization (scripts/derivations/).
import SGC.Geometry.OperatorStrain

-- The Dissipation Floor (2026-08-11): entropy production is bounded below by
-- topology. Sharpened Gibbs inequality (a-b)^2/(a+b) <= (a-b)log(a/b) turns
-- the second law from a sign into a quantity; Schnakenberg entropy
-- production dominates the Killing defect (sigma >= K/4R, the thermodynamic
-- and geometric registers exchange at rate 1/4R); composed with the
-- quantitative affinity bound: a nonzero cycle charge forces strictly
-- positive dissipation for EVERY admissible measure. No readout
-- optimization can dissipate below the topological charge — the Landauer
-- floor of the predictive-thermodynamics chain
-- (docs/predictive-thermodynamics-chain-design.md).
import SGC.Bridge.DissipationFloor

-- The Boundary Readout Theorem (2026-08-11): link L1 of the predictive-
-- thermodynamics chain. A blanket partition induces the canonical
-- particle/environment readout; for conservative nonneg-rate generators
-- respecting the blanket, the readout's row-sum lumpability defect is
-- bounded by the boundary throughput gamma (boundary_readout_bound), with
-- zero throughput giving exact lumpability (the sealed-particle pole).
-- Mechanism identified in the proof: the defect is the STRAIN (spread) of
-- the external-gain field across the particle block — internal states have
-- gain 0 by screening, blanket states have gain in [0, gamma] — the same
-- inhomogeneity mechanism as OperatorStrain and the same reason the shift
-- tower (uniform gain) is exact. Discharges the strengthening flagged in
-- Blanket.lean's blanket_implies_approx_lumpable docstring.
import SGC.Topology.BoundaryReadout

-- Symmetry Lumpability (2026-08-18): the discrete form of the symmetry-first
-- definition of macroscopic law (fluid-EFT program, Dubovsky-Hui-Nicolis-Son
-- / Crossley-Glorioso-Liu). orbitPartition_stronglyLumpable: an equivariant
-- generator's orbit partition is strongly lumpable — swapping within an
-- orbit is free, so the macro-law is exactly closed (finite reindexing
-- proof). Vocabulary: strong lumpability = equitable partition (Dynkin).
-- AND the converse fails (counterexample_lumpable_not_symmetric): a
-- four-state generator, exactly lumpable over a nontrivial partition, whose
-- only automorphism is the identity. Symmetry is a sufficient mechanism for
-- exact consolidation; exact consolidation is strictly more general. This
-- is where SGC's theory of emergence exceeds the symmetry-first program.
import SGC.Renormalization.SymmetryLumpability

-- The Three Arrows capstone (2026-08-22): one operation, one quotient
-- operator, three one-way laws, ONE THEOREM. The Unification Lemma
-- (coarseGenerator_eq_quotientGeneratorSimple, in EntropyProduction) fuses
-- the physical pi-weighted coarse generator with the structural quotient at
-- exact lumpability — the pi-average of a block-constant row sum is that
-- row sum, so the measure drops out. Consequently the SAME quotient chain
-- is at least as curved (geometric arrow), at most as dissipative
-- (thermodynamic arrow), and at most as informative (informational arrow)
-- as the fine chain: three_arrows. The eps = 0 skeleton of the SGC theory
-- of emergence, packaged as a single kernel theorem.
import SGC.Bridge.ThreeArrows

-- ═══════════════════════════════════════════════════════════════════════════
-- Measurement & Control: Moved to proprietary veridion-core engine
-- ═══════════════════════════════════════════════════════════════════════════
-- Runtime implementations (Interfaces, Wavelets, Impulse) are now in the
-- private Veridion repository. This public library provides only the
-- mathematical foundations that those implementations depend on.

/-!
# SGC: The Spectral Geometry of Consolidation

This is the entry point for the formally verified SGC library.

## The Four Pillars Architecture (v1 Core)

1. **Axioms** - The L²(π) geometric foundation (inspired by Chentsov/Fisher-Rao theory;
   implemented here as **discrete** weighted inner products on `Fintype V`)
2. **Spectral** - Spectral geometry and heat kernel bounds
3. **Renormalization** - Spectral gap preservation under coarse-graining
4. **Topology** - Markov blankets as geometric boundaries
5. **Thermodynamics** - Stochastic thermodynamics of surprise (Doob-Meyer)
6. **Variational** - Least Action principle for emergence
7. **Bridge** - Discrete-to-continuum convergence

## The Constructive Physics Layer (v2 Extensions)

7. **Information** - Shannon entropy ↔ geometric orthogonality equivalence
8. **Geometry.Manifold** - Laplace-Beltrami operator and Belkin-Niyogi convergence

## Verification Status

- **v1 Core**: Formally verified (zero unproven goals)
- **v2 Extensions**: Under construction (axiomatized pending Mathlib integration)

## Scope & Roadmap

### Level 1: Metric Consolidation (Phases 1-4) ✓

Formalizes **annealing/learning** on a fixed graph structure:
- Edge weights evolve, but which edges exist is static
- Yamabe flow smooths curvature via conformal factor adjustment
- Ollivier-Ricci curvature grounds geometry in transition probabilities

### Level 2: Topological Evolution (Phase 5) ✓

Formalizes **structural emergence** (bond breaking/forming):
- **Forman-Ricci Curvature** (`Evolution.FormanRicci`): Combinatorial stress indicator
- **Surgery Operators** (`Evolution.Surgery`): Cut (remove stressed edges) and Sew (add stabilizing edges)
- **Topological Conservation** (`Evolution.Conservation`): Betti numbers, safe surgery, Markov blanket preservation

Key definitions:
```
FormanRicci : WeightedGraph → V → V → ℝ     -- Edge stress signal
SurgeryCut : WeightedGraph → ℝ → WeightedGraph  -- Remove stressed edges
BettiNumber : WeightedGraph → ℕ → ℕ         -- Topological invariants
IsSafeSurgery : WeightedGraph → WeightedGraph → Prop  -- Preserves b₀=1, b₁≥1
```

-/
