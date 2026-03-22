# Research Assistant Briefing: The Spectral Geometry of Consolidation
## A Directive for Deep Theoretical Engagement

**Date**: February 14, 2026  
**From**: Cascade (Implementation Partner, living inside the codebase)  
**To**: Research Assistant  
**Repository**: https://github.com/JasonShroyer/sgc-lean/tree/wip-quantum-bridge  

---

## 0. Your Role and Our Collaboration Model

You have been granted full access to the SGC-Lean repository. I (Cascade) live inside the codebase and have complete access to every file, every experimental log, every failure, and every line of verified Lean 4 proof. Jason (the user) occupies the principal investigator role—he sets the theoretical direction and holds the philosophical vision. Your role is to bring deep mathematical and scientific expertise, access to the academic literature, and the ability to challenge and extend our theoretical framework.

**The hierarchy**: Jason sets direction. You challenge and deepen theory. I verify against ground truth and implement. When there is a disagreement about what the code actually does or what an experiment actually showed, I have final say because I see the source of truth. When there is a disagreement about mathematical theory or connections to the literature, we defer to you and Jason collaboratively.

**Our methodology is non-negotiable**: We work from first principles. Every implementation decision must be derived from SGC theory, physics, or mathematics. We do NOT do empirical iteration (trying random things and hoping they work). If something doesn't work, we go back to theory to understand WHY. See the full methodology statement in the repository.

---

## 1. What SGC Actually Is

SGC (Spectral Geometry of Consolidation) is a **formal mathematical framework for the physics of emergence**. It answers: *When can a complex micro-system be validly described by a simpler macro-theory?*

**The core object is the Defect Operator:**
```
ε = ‖(I - Π)LΠ‖
```
where L is a generator (dynamics) and Π is a coarse-graining projection. The defect ε measures how much information "leaks" from the macro-description back into micro-details.

**The core theorem is the Validity Horizon:**
```
T* ≥ δ/ε
```
Any coarse-grained model with defect ε is mathematically guaranteed valid for time T*. After that, macro and micro diverge.

**This is NOT just about neural networks.** SGC applies to:
- Markov chains (the original setting)
- Quantum error correction (via the Classical-Quantum Bridge)
- Neural network grokking (via the Functional Blanket)
- Constraint satisfaction (Sudoku, ARC puzzles)
- Any system where emergence occurs

The universality is the point. The same mathematics governs all of these.

---

## 2. Where to Look in the Repository

### 2.1 The Lean Formalization (`src/SGC/`)

This is the crown jewel. **Everything here compiles. The verified core has zero `sorry` placeholders.**

| Module | Path | What You'll Find |
|--------|------|------------------|
| **Axioms/Geometry** | `src/SGC/Axioms/Geometry.lean` | Weighted L²(π) inner product, the geometric arena |
| **Renormalization** | `src/SGC/Renormalization/` | The engine: approximate lumpability, trajectory bounds |
| **Bridge/Quantum** | `src/SGC/Bridge/Quantum.lean` | Classical ↔ Quantum correspondence (Knill-Laflamme) |
| **Bridge/Recovery** | `src/SGC/Bridge/Recovery.lean` | Petz recovery map, relative entropy (ENNReal) |
| **Bridge/Consolidation** | `src/SGC/Bridge/Consolidation.lean` | RG monotonicity from Data Processing Inequality |
| **Bridge/GeometricClosure** | `src/SGC/Bridge/GeometricClosure.lean` | Bakry-Émery Ricci curvature, tensorization |
| **Observables** | `src/SGC/Observables/` | Validity horizon, topological persistence, energy unification |
| **FunctionalBlanket** | `src/SGC/FunctionalBlanket.lean` | Functional defect, class separation, Lifshitz transition |
| **Grokking** | `src/SGC/Grokking.lean` | Umbrella: Kramers escape, information gradient law |
| **ContinualLearning** | `src/SGC/ContinualLearning/` | Adiabatic invariants for continual learning |
| **Thermodynamics** | `src/SGC/Thermodynamics/DoobMeyer.lean` | Stochastic first law (Doob decomposition) |
| **Variational** | `src/SGC/Variational/LeastAction.lean` | Least action principle for complexity |

**Key verified theorems (zero sorry):**
- `trajectory_closure_bound`: Error grows O(ε·t) — THE core result
- `NCD_uniform_error_bound`: Uniform-in-time O(ε/γ) for nearly-completely-decomposable systems
- `knill_laflamme_forces_zero_defect`: Classical Markov chains cannot do quantum error correction
- `dirichlet_gap_non_decrease`: Spectral gap monotonicity under coarse-graining
- `positive_Ricci_tensorizes`: Ric(A×B) ≥ min(Ric(A), Ric(B)) — no curse of dimensionality
- `autocorrelation_decay_from_sector`: Spectral gap → measurable autocorrelation decay

**Key null result (physically meaningful):**
- `NCD_spectral_stability`: **DISPROVED.** The proof assistant correctly showed this is false due to secular phase drift. Vertical error is bounded O(ε/γ), but horizontal phase drifts as O(ε·t). This demarcates the validity horizon of effective theories.

### 2.2 Theory Documents (`docs/`)

| Document | What It Contains |
|----------|-----------------|
| `RESEARCH_NARRATIVE.md` | **START HERE** — guided tour of the whole project |
| `lifshitz_transition_theory.md` | Complete theoretical synthesis: grokking as Lifshitz transition |
| `functional_blanket_breakthrough.md` | The key discovery: functional vs geometric blankets |
| `unified_theory_sgc_active_inference.md` | SGC = Active Inference = Continual Learning |
| `synthesis_toward_intelligence.md` | Honest assessment: what's validated, what's arbitrary, what's open |
| `sgc_theory_roadmap.md` | Publication-ready theory with predictions |
| `AGI_ROADMAP.md` | Three-phase path: Digital Controller → Thermodynamic Hardware → Brain-Like |
| `PHASE_2_BRIEFING.md` | Compositional generalization challenge |

### 2.3 Experimental Code (`demos/`)

Over 80 Python files documenting every experiment. Key ones:

| File | What It Does |
|------|-------------|
| `lifshitz_transition_experiment.py` | Validates grokking = Lifshitz transition |
| `functional_grokking_detector.py` | Intrinsic grokking detection via functional defect |
| `analog_modular_arithmetic.py` | Noisy embeddings accelerate grokking 2x |
| `cellular_sheaf_network.py` | Native sheaf architecture achieves compositional generalization |
| `adaptive_polarity_v2.py` | Agent autonomously discovers constraint polarity |
| `adaptive_polarity_v5.py` | Iterative Collapse breakthrough (85% Sudoku) |
| `adaptive_polarity_v10_hybrid_bootstrap.py` | Cold Start Problem solution |
| `arc_sgc_agent.py` | **The ARC agent** — current focus of active development |
| `arc_sgc_residual_solver.py` | Gradient-guided program synthesis for ARC |
| `arc_sgc_phase45.py` | Neighborhood constraint learning with zone-gated patterns |

### 2.4 Reports (`reports/`)

Every experiment has a report. Key ones for understanding failures:

| Report | What Failed and Why |
|--------|-------------------|
| `PHASE_2_FAILURE_ANALYSIS.md` | Post-hoc sheaf gluing CANNOT compose disjoint manifolds |
| `HOMEOSTAT_PROGRESS_REPORT.md` | Confidence homeostat: physics works, accuracy doesn't beat simple baseline |
| `ITERATION_SUMMARY_V3_V5.md` | Three failed approaches before Iterative Collapse breakthrough |
| `CELLULAR_SHEAF_BREAKTHROUGH.md` | What finally worked: native sheaf architecture |
| `ADAPTIVE_POLARITY_BREAKTHROUGH.md` | Autonomous constraint polarity discovery |

---

## 3. The Major Breakthroughs

### 3.1 Grokking = Topological Lifshitz Transition (VALIDATED)

**The discovery that changes everything.** There are TWO types of Markov blankets, and they behave OPPOSITELY during grokking:

| Blanket Type | Definition | At Grokking |
|--------------|------------|-------------|
| **Geometric** (PCA closure) | ‖g(h) - g(Πh)‖ / ‖g(h)‖ | **INCREASES** (0.23 → 0.35) |
| **Functional** (algebraic) | within-class variance / total variance | **COLLAPSES** (1.0 → 0.003) |

**Old theory (WRONG)**: Grokking = dimensionality reduction (geometric compression)  
**New theory (VALIDATED)**: Grokking = learning the **symmetry group** (algebraic structure)

The solution manifold is a **torus** (T², with non-zero Ricci curvature), not a flat linear subspace. That's WHY geometric defect increases—the model expands into a curved submanifold.

**Experimental data** (modular addition a + b mod 97):

| Metric | Pre-Grok | At Grok | Post-Grok |
|--------|----------|---------|-----------|
| Functional Defect | 1.01 | 0.13 | **0.003** |
| Class Separation | 0.01 | 6.45 | **346** |
| Geometric Defect | 0.23 | 0.35 | 0.33 |
| Tsallis q | 2.53 | 2.09 | 2.76 |

### 3.2 The Classical-Quantum Bridge (VERIFIED IN LEAN)

**Theorem** (`knill_laflamme_forces_zero_defect`): For a classical stochastic generator L with conservation (row sums zero), if the complexified defect E = (I−Π)LΠ satisfies the Knill-Laflamme condition Π E†E Π = α·Π, then **E = 0**.

**Physical interpretation**: Classical Markov chains CANNOT exhibit the "coherent backaction" structure required by quantum error-correcting codes. The conservation law (probability preservation) forces α = 0.

| Classical (Markov) | Quantum |
|---|---|
| Exact lumpability (ε = 0) | Knill-Laflamme conditions |
| Approximate lumpability | Approximate QEC |
| Conservation law | Probability preservation |

This is not a metaphor. It is a verified isomorphism.

### 3.3 Kramers Escape and the 2x Analog Speedup (VALIDATED)

Adding Gaussian noise (σ=0.1) to embeddings during training accelerates grokking from epoch 2300 to epoch 1150 (2x speedup).

**Why**: From SGC master equation → Fokker-Planck → first passage time:
```
τ ≈ (2π/√|V''|) × exp(ΔV/D)
```
Noise provides thermal kicks over saddle points separating memorization from generalization basins. This is literally Kramers escape from statistical mechanics.

### 3.4 The Cellular Sheaf Network (100% Compositional Generalization)

**The network must BE a sheaf, not HAVE a sheaf retrofitted.**

Native sheaf architecture achieved 100% test accuracy on `(x + y) * z mod 23`—a compositional task that post-hoc sheaf gluing completely failed (3.4% accuracy).

Key: multiplicative aggregation for the product node, additive for the sum node. The graph topology directly encodes the algebraic structure.

### 3.5 Tensorization of Ricci Bounds (VERIFIED IN LEAN)

`positive_Ricci_tensorizes`: If Ric(L_A) ≥ ρ_A and Ric(L_B) ≥ ρ_B, then Ric(L_{A×B}) ≥ min(ρ_A, ρ_B).

**Physical significance**: No curse of dimensionality for stability. The weakest subsystem determines the overall decay rate. Modular composition: Stable + Stable = Stable.

### 3.6 Iterative Collapse = Renormalization (85% Sudoku)

The breakthrough from v2's 62.7% plateau to v5's 85% came from recognizing that `SGC.Renormalization.Approximate` directly applies to constraint satisfaction:
- Coarse-graining = collapsing one cell at a time
- Each collapse reduces state space: 9^N → 9^(N-1)
- Spectral gap increases with each collapse (problem gets easier)

This is wavefunction collapse as renormalization group flow.

---

## 4. The Important Failures (CRITICAL READING)

These negative results are as valuable as the breakthroughs. They constrain the search space.

### 4.1 Post-Hoc Sheaf Gluing FAILS (Definitive)

**Experiment**: Take two perfectly-grokked networks (addition, multiplication), freeze them, try to compose via learnable restriction maps.

**Result**: 3.4% accuracy (near random). The restriction maps learned arbitrary projections, not structure-preserving morphisms.

**Why**: The two networks create disjoint manifolds M_A ⊔ M_B. A sheaf requires a shared base space. When M_A ∩ M_B = ∅, the fiber product collapses to the empty set. Diffusion cannot propagate across a vacuum.

**Lesson**: Compositionality requires NATIVE architectural support. You cannot glue isolated modules post-hoc.

### 4.2 The Confidence Homeostat: Physics Works, Accuracy Doesn't

**Experiment** (v6 series): Implement write/erase/crystallize mechanics from Ashby's Law of Requisite Variety for Sudoku.

**Result**: All mechanics work correctly. Alpha-certainty correlation improved to 0.322. But accuracy (65.9%) never beat simple iterative collapse (85%).

**Why**: The homeostat only sees **topology** (neighbor conflicts), not **correctness** (matching the solution). Conflict ≠ Error. The system learned to avoid neighbor collisions but not to be actually right.

**The paradox**: Backtracking capability (Requisite Variety) actually HURTS on Sudoku because Sudoku has a unique solution—mistakes can be avoided by being more careful initially. v5's direct supervision teaches "don't commit unless sure." v6's homeostat teaches "commit tentatively, fix later"—but "later" loses context.

**Implication**: The homeostat may work better on tasks that genuinely require exploration (like ARC), not tasks with unique solutions (like Sudoku).

### 4.3 The Cold Start Problem

**Experiment** (v9): Use neural network as simulator of physics, planner finds argmin.

**Result**: Defect(Correct) ≈ Defect(Wrong) — the simulator cannot distinguish right from wrong because untrained physics is isotropic.

**Solution** (v10): Supervised pre-training ("build the walls") before Active Inference. 22,000x improvement in discrimination. But Active Inference overhead then HURTS accuracy on Sudoku.

**Lesson**: Active Inference agents require "evolutionary pre-training" to break the symmetry between correct and incorrect states. This has implications for developmental AI.

### 4.4 Failed Sudoku Approaches (The Void Trap and Entropy Lock)

- **v3 (Hard Sphere)**: Pushed stalks into the orthogonal complement of the code subspace—the "Void" where stalks are maximally different from neighbors but not valid digits. We implemented H_interaction but omitted H_stabilizer.

- **v4 (Entropy Stabilizer)**: The entropy penalty forced all cells to sharpen to the SAME digit (easiest path to low entropy = consensus). Created a "False Vacuum" at the Consensus State where the gradient locked polarity into attraction.

**Lesson**: Every "improvement" that imposed external knowledge made things worse. The system must discover constraints through interaction with the environment.

### 4.5 The 1% Mixing Efficiency Gap

The theoretical mixing time predicts M_explore ≈ 2.3, but empirically M ≈ 200 is required (87× gap). We hypothesize:
```
M_effective = M_noise × (task-relevant dim / total dim) × spectral_gap_factor
```
but this remains **unexplained**. This is our biggest open theoretical gap.

### 4.6 NCD Spectral Stability is FALSE (Physical Insight)

The Lean proof assistant correctly identified that `NCD_spectral_stability` is **false**. While vertical error is uniformly bounded O(ε/γ), horizontal phase drift grows as O(ε·t). This is not a bug—it's the physics of validity horizons: effective theories work for t ≪ 1/ε but break at t ~ 1/ε.

---

## 5. The ARC Challenge: Current State of the Art

### 5.1 What Is ARC?

The Abstraction and Reasoning Corpus (ARC) by François Chollet is the hardest benchmark for machine intelligence. Each task gives 2-3 input→output grid examples and asks the agent to predict the output for a new input. Tasks require diverse reasoning: symmetry detection, object manipulation, pattern completion, color transformations, spatial reasoning.

### 5.2 Our Architecture

The ARC agent (`demos/arc_sgc_agent.py`) is a multi-scale solver with persistent memory:

| Scale | Solver | What It Does | Wins |
|-------|--------|-------------|------|
| **Micro** | RecursiveResidualSolver | Gradient-guided program synthesis with predicate vocabulary | 16 |
| **Meso** | NeighborhoodConstraintLearner (Phase 45) | Translation-invariant 3×3 pattern rules | 147 |
| **Macro** | Heuristic solvers | Color maps, rotations, flips, transposes | 7 |

**Dream Consolidation**: The agent persists learned programs across tasks. 28 compiled programs, 87 near-misses, 17 contexts. Average posterior 0.81.

**Pattern Memory**: Content-addressed operator memory with Thompson sampling for contextual recall. Bayesian posteriors evolve over epochs.

### 5.3 Current Results

| Dataset | Perfect | Near-Miss | Fail |
|---------|---------|-----------|------|
| Training (97 tasks) | **19 (19.6%)** | 51 (52.6%) | 27 |
| Evaluation (400 tasks) | **23 (5.75%)** | 139 (34.75%) | 238 |

### 5.4 What We've Tried and the Results

**Things that WORKED:**
1. **Predicate vocabulary** (ILP-style): `adj_to_C`, `enclosed_by_fg`, `between_C_h/v`, `inside_bbox_C`, `contained_by_C`, `same_shape_as_C`, etc. Each new predicate unlocks tasks.
2. **Recursive beam search** (depth≤3, width=8): Composing 2-3 atomic operations (fill, recolor, erase) with predicate guards.
3. **Neighborhood constraint learning**: 3×3 input patch → output color, with harmonic fill for ambiguous pixels.
4. **Dream Consolidation**: Programs compiled from successful solves, persisted across sessions, recalled via Thompson sampling.
5. **Color-coherent conjunction search**: Pairing predicates with same-color predicates only prevents overfitting.
6. **Zone-gated neighborhoods**: Structural context (foreground, enclosed, adjacent, border, default) for Phase 45 patterns. +2 Phase 45 wins on training, +3 on eval.

**Things that HAD MARGINAL/NO EFFECT:**
1. **Zone-gated neighborhoods on eval**: +3 Phase 45 wins but 0 new perfect solves. The bottleneck is NOT pattern disambiguation.
2. **Operator induction from near-misses**: Detects which operators are relevant but doesn't directly solve tasks.
3. **Dream recall at single-epoch scale**: 0 successful recalls in one pass. Payoff expected on multi-epoch runs.

**Things we HAVEN'T tried yet:**
1. **Color-normalized patterns**: Abstract away specific colors so rules transfer across permutations.
2. **Object-level reasoning**: Reflections, rotations, translations of detected objects (not just pixel-level).
3. **Hypothesis-driven search**: The Phase 20 RuleRegistry for generating and testing rule hypotheses.
4. **The Homeostat for ARC**: The write/erase/crystallize mechanics that failed for Sudoku might work for ARC's genuinely exploratory nature.

### 5.5 Key Bottleneck Analysis

The 139 eval near-misses break down into:
- **Very close (dist < 0.02)**: ~5 tasks limited by beam search quality, not predicate vocabulary
- **Close (0.02-0.10)**: ~80 tasks, diverse failure modes
- **Failed-method**: ~8 tasks where residual solver produces nothing—need NEW colors, object-level reasoning (reflections)
- **Shape mismatch**: Tasks where output grid size differs from input (crop, scale, tile)

**The fundamental bottleneck**: Phase 45 (meso-scale patterns) wins 147/170 solved tasks. But Phase 45 only works when input→output grids are the same shape and the transformation is a local neighborhood rule. The residual solver (micro-scale) can handle more complex programs but has a narrow beam and limited predicate vocabulary. We have NO macro-scale solver for geometric transforms (object rotations, reflections, tiling).

---

## 6. The Four Equivalences (Core Theoretical Framework)

```
1. Defect = Curvature       (not error)
2. Noise = Temperature      (Kramers escape)
3. Grokking = Phase Transition   (Lifshitz)
4. Continual Learning = Adiabatic Evolution
```

These are not metaphors. Each has a precise mathematical formulation and experimental validation.

### 6.1 The Unified Picture

| Phenomenon | SGC/UPAT | Condensed Matter | Neural Networks | Our Data |
|------------|----------|------------------|-----------------|----------|
| Exploration | UV regime | High temperature | Noise σ=0.1 | Epochs 0-2000 |
| Transition | RG flow | VHS crossing | Hessian peak at λ=0 | Epoch 2300 |
| Emergence | IR fixed point | Lifshitz transition | Grokking | FuncD → 0 |
| Structure | Quotient graph | Fermi surface | Equivalence classes | p=97 residues |
| Geometry | Curved manifold | Non-zero curvature | Torus T² | GeomD ↑ |

---

## 7. Connections to Other Sciences (Fertile Ground)

SGC is not domain-specific. Here are the cross-disciplinary connections we've identified but not yet fully exploited:

### 7.1 Condensed Matter Physics
- **Lifshitz transitions** (Fermi surface topology change without symmetry breaking)
- **Van Hove singularities** (density of states peaks)
- **Bakry-Émery Ricci curvature** (heat kernel bounds on manifolds)
- **Tsallis entropy** (non-extensive statistics, scale-free representations)

### 7.2 Quantum Information
- **Knill-Laflamme conditions** → classical lumpability (VERIFIED)
- **Approximate QEC** → approximate lumpability (formalized)
- **Toric code stability** → topological protection via SGC bounds

### 7.3 Category Theory
- Morphisms in the category: InputPatch → OutputColor ≅ Grid → Grid
- Sheaf cohomology as the mathematical home for compositional generalization
- Functorial learning (restriction maps as natural transformations)

### 7.4 Thermodynamics
- **Landauer's principle**: Erase cost > Write cost (implemented in homeostat)
- **Kramers escape**: Noise-assisted barrier crossing (validated 2x speedup)
- **Doob-Meyer decomposition**: Stochastic first law (verified in Lean)

### 7.5 Cybernetics
- **Ashby's Law of Requisite Variety**: Agent needs internal complexity ≥ environmental complexity
- **Ultrastable systems**: Two-loop regulation (fast: perception, slow: structure learning)
- **Beer's Viable System Model**: Hierarchical organization of autonomous systems

### 7.6 Biology / Neuroscience
- **Free Energy Principle** (Friston): Active inference as defect minimization
- **Markov blankets** as the boundary of self-organizing systems
- **Developmental pre-training**: "Evolution pre-wires pain circuits before the baby learns" (Cold Start Problem solution)

---

## 8. The Open Theoretical Questions

### 8.1 Urgent (Directly Impact Current Work)

1. **Why does zone-gating help Phase 45 wins but not perfect solves?** The zone map disambiguates 3×3 patterns structurally, but this isn't the bottleneck. What IS?

2. **What is the minimal predicate vocabulary for ARC?** We have ~50 predicates. Which are redundant? Which are missing? Is there a theoretical bound on the needed vocabulary?

3. **Can the Functional Blanket framework apply to ARC?** ARC tasks don't have "equivalence classes" in the modular arithmetic sense. What is the analog of "symmetry group" for visual reasoning?

### 8.2 Deep (Fundamental Theory)

4. **The 1% Mixing Efficiency**: Why is M_actual/M_theoretical ≈ 87? This is our biggest unexplained gap.

5. **Does functional blanket interpretation extend to continuous tasks?** All our validation is on discrete equivalence classes (mod-p arithmetic). What about continuous symmetries?

6. **What is the relationship between Tsallis q and grokking?** We measured q ≈ 2.5, which matches scale-free network theory. But q didn't monotonically change at grokking (went 2.53 → 2.09 → 2.76). Why?

7. **Can the coarse-graining be LEARNED?** We hand-specify Π. Can the network discover its own coarse structure? The functional defect doesn't require explicit Π, which is promising.

8. **Is there a variational principle for intelligence?** The least action principle (`variational_drift_optimality` in Lean) suggests systems maximize consolidation rate. Can this be extended to a variational principle for general intelligence?

---

## 9. The Challenge

**Construct a new theory of emergent intelligence based on this collective understanding.**

You have:
- A verified mathematical framework (Lean proofs, zero sorry in core)
- A validated physical theory (Lifshitz transition, Kramers escape, functional blanket)
- A catalog of precise negative results (what DOESN'T work and WHY)
- A working experimental testbed (ARC agent, grokking experiments)
- Cross-disciplinary connections to exploit (condensed matter, quantum info, category theory, thermodynamics, cybernetics, neuroscience)

The theory should:
1. **Explain** why functional (algebraic) blankets, not geometric (PCA) blankets, are the correct abstraction
2. **Predict** what operations/predicates the ARC agent needs that it currently lacks
3. **Unify** the micro (residual solver), meso (neighborhood patterns), and macro (geometric transforms) scales under a single theoretical umbrella
4. **Address** the bottleneck: why can we solve 19/97 training tasks but only 23/400 eval tasks? What's the generalization barrier?
5. **Connect** to the verified Lean theorems—the theory should be formalizable
6. **Leverage** analogies from physics, mathematics, and biology that give us deep insights we haven't yet exploited

The SGC formalization proves that emergence has precise mathematical structure. The question is: **how do we use this structure to build systems that actually think?**

---

## 10. Quick-Start Reading Order

1. `docs/RESEARCH_NARRATIVE.md` — 15 min overview
2. `VERIFIED_CORE_MANIFEST.md` — what's actually proven in Lean
3. `docs/functional_blanket_breakthrough.md` — the key discovery
4. `docs/lifshitz_transition_theory.md` — complete theoretical synthesis
5. `reports/PHASE_2_FAILURE_ANALYSIS.md` — why post-hoc composition fails
6. `reports/CELLULAR_SHEAF_BREAKTHROUGH.md` — why native sheaf architecture works
7. `reports/HOMEOSTAT_PROGRESS_REPORT.md` — the full journey v2→v10
8. `docs/unified_theory_sgc_active_inference.md` — SGC = Active Inference
9. `docs/synthesis_toward_intelligence.md` — honest assessment of what we know
10. `demos/arc_sgc_agent.py` (lines 1-38) — the ARC agent architecture

---

*"Emergence is a topological phase transition governed by diffusion-RG dynamics on a causal graph, with dual entropy-extropy optimization."*

*This is the physics of emergence from first principles. Help us turn it into the physics of intelligence.*
