# Second-Law Formalization Sprint — 2026-05-25

**Branch**: `sprint/entropy-axiom-closure-2026-05-25` (chained off `sprint/brownian-phasediagram-celegans-2026-05-19`)

**Headline**: The **second law of thermodynamics for finite Markov chains** is now PROVED in the WKL₀-comfortable baseline (kernel axioms only), and FluxDecomposition.lean is reduced to a single remaining axiom (the spectral non-normality conjecture).

---

## What was closed

| Axiom | Status | Strategy |
|---|---|---|
| `normal_of_self_adjoint` | **PROVED** | Trivial: `L = L†` ⇒ `L·L − L·L = 0` via `sub_self`. |
| `pi_adjoint_inner` | **PROVED** | Both sides reduce to canonical `∑x∑y π(x)M(x,y)f(x)g(y)`; match via `Finset.sum_comm` + alpha-equivalence. |
| `sector_condition_companion` | **PROVED** | `dirichlet_form_eq_symmetric_part` + `inner_pi` linearity in negation. |
| `gaspard_maes_bridge` | **STAGED** | Renamed to `gaspard_path_space_identity`; backward-compatible `@[deprecated]` alias kept. |
| `entropy_production_nonneg` | **PROVED** | The second law: σ ≥ 0 via pointwise Gibbs inequality. |
| `zero_entropy_implies_zero_current` | **PROVED** | σ = 0 ⇒ J = 0 via `Finset.sum_eq_zero_iff_of_nonneg` + Gibbs equality. |

**Net axiom count delta**: −5 (one rename) in `Thermodynamics/`.

**FluxDecomposition.lean is now at 1 axiom** — the spectral conjecture `non_normality_from_flux` (a genuine open research problem).

---

## The Gibbs-term core

Both Sprint-2 closures rest on a single conceptual unit:

```lean
lemma gibbs_term_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * Real.log (a / b)

lemma gibbs_term_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) * Real.log (a / b) = 0 ↔ a = b
```

These two lemmas are the **atomic certifiers of irreversibility**:

- **Inequality** ⇒ second law σ ≥ 0 (sum of non-negatives).
- **Equality condition** ⇒ detailed-balance characterization (each summand zero ⇒ each ratio = 1).

The Gibbs term `(a − b) · log(a/b)` is, mathematically, the **single-pair entropy production**. Aggregating over all pairs via the Schnakenberg formula gives the system-level σ. The structural-shape pattern is:

```
∑(non-neg single-pair quantities) = 0
       ⇒ ∀ pair, single-pair quantity = 0
       ⇒ ∀ pair, the pointwise physical relation holds (here: π_x L_{xy} = π_y L_{yx})
```

This pattern recurs throughout statistical mechanics. The Lean formalization makes it crystalline: `Finset.sum_eq_zero_iff_of_nonneg` is the *formal carrier* of this case-equality argument.

**Conceptual implication**: there's a natural opportunity to factor out `gibbs_pair_ep : ℝ → ℝ → ℝ := fun a b => (a-b) * Real.log (a/b)` as a first-class object with its own algebraic laws (convexity, scaling, symmetry under swap). This would deduplicate the Schnakenberg derivations across this module and `EntropyProduction.lean`.

---

## Formalization-vs-textbook distinction discovered

The textbook statement of the second law for Markov chains assumes "L is a valid generator". The formal proof in Lean requires:

```lean
hL_nonneg : ∀ x y, x ≠ y → 0 ≤ L x y
```

as an **explicit hypothesis**, beyond the previous `hL_irred : ∀ x y, x ≠ y → L x y > 0 → L y x > 0`. Without `hL_nonneg`, Lean's junk-value convention `Real.log r = 0` for `r ≤ 0` creates pathological counterexamples (e.g., `L_{xy} = 0` with `L_{yx} < 0` yields σ = 0 with J ≠ 0).

**This is not a defect of the formalization** — it is the formal counterpart of the textbook's implicit "for a Markov generator" precondition. Lean refuses to let us forget this premise. Once added, the theorem is straightforwardly true.

**General pattern**: physical-law formalization in Lean tends to surface implicit textbook preconditions as explicit hypotheses. This is one of the most valuable outputs of the formalization process — it identifies precisely *what is being assumed*.

---

## Path-space identity staging

`gaspard_maes_bridge` was renamed to `gaspard_path_space_identity` and given a detailed 4-step staged docstring:

1. **Definitional**: σ_hid = path-space KL rate between forward and time-reversed coarse-grained measures. *(Standard; just rewriting the definition once path measures exist in Lean.)*
2. **The deep step**: KL rate ≥ Dirichlet form ℰ(Df). *(Genuinely open — requires Donsker-Varadhan or Maes-Netočný fluctuation symmetry.)*
3. **Poincaré inequality**: ℰ(g) ≥ γ‖g‖²_π for g ⊥ 1. *(Already formalized in `Lumpability.lean` / `QuotientGenerator.lean` via `DirichletForm` and `DirichletGap`.)*
4. **Sup over test functions**: γ · ‖D‖²_op ≤ σ_hid. *(Algebra given steps 2 and 3.)*

The gap is now **localized**: step 2 is the single open ingredient. Future work would formalize:

- Continuous-time path measures on irreducible finite-state CTMCs.
- The time-reversal operator on those path measures.
- The Maes-Netočný fluctuation symmetry (or Donsker-Varadhan).

None of this currently exists in Mathlib in the form needed for finite Markov chains. The next sprint targeting this should likely start in `Mathlib/Probability/`.

---

## Audit surface

| | Before May 19 | After May 19 sprint | After this branch |
|---|---|---|---|
| Audited flagship theorems | — | 35 | **50** |
| At WKL₀ baseline (kernel only) | — | 34 | **46** |
| With named physical axioms | — | 1 | **4** |
| Distinct named axioms in play | — | 1 | **3** |

The **leverage marker** — `hidden_entropy_lower_bound` audit line — is unchanged in form but now points at `gaspard_path_space_identity` (more accurate name); closing the path-space identity removes the dependency. Same pattern for `efficiency_requires_prediction` and `hidden_entropy_bounded_by_defect`.

---

## Conceptual leaps to investigate (peripheral vision)

These are observations from this sprint that deserve follow-up. They are recorded here, not implemented:

### 1. Gibbs-term as a first-class object

Factor out `gibbs_pair_ep` with its own algebraic structure. Likely useful sites:
- `Thermodynamics/EntropyProduction.lean` — Schnakenberg formula direct expression.
- `InformationGeometry/FisherKL.lean` — discrete KL is a sum of `gibbs_pair_ep`-like terms.
- `Bridge/Quantum.lean` — quantum relative entropy has the same atomic structure.

### 2. The Tensor Logic × SGC connection (from `theory_context/Tensor Logic × SGC Synthesis.md`)

Pedro Domingos's Tensor Logic (arXiv:2510.12269) shows that **Datalog inference and tensor contraction are the same operation**. Applied to SGC:

- The defect operator `ε(Π, L) = ‖(I − Π) L Π‖` (formalized in `Renormalization/Approximate.lean`) becomes a **loss function** in a differentiable computational graph.
- Optimal partition Π is discovered by **gradient descent on the defect**, equivalently by **Tucker decomposition of the transformation tensor**.
- This is the functor `F: Observations → Partitions` that SGC has been treating as given.

**Concrete next sprint**: a Python prototype `demos/sgc_tensor_logic_arc.py` that uses tensor decomposition on ARC tasks, with the formalized defect operator as the verification oracle. The Boolean ↔ continuous "temperature knob" of Tensor Logic interpolates between exact reasoning (T=0, current SGC) and learnable inference (T>0).

This would close the loop: the Lean-formalized objects become **executable** and **differentiable** without sacrificing verifiability.

### 3. Schnakenberg-like patterns

The "sum of non-negatives = 0 ⇒ each is 0" pattern recurs in:
- Detailed balance characterization (this sprint).
- Maximum-entropy variational principles.
- Bregman-divergence positivity.
- Convex-function inequalities (Jensen, log-sum, etc.).

A general-purpose `Sum.zero_of_nonneg_summands_eq_zero` tactic or simp set might be worth packaging. Mathlib's `Finset.sum_eq_zero_iff_of_nonneg` is the carrier; a `decide_pointwise_zero` macro could chain it with field-specific positivity proofs.

### 4. Junk-value pattern detection

`Real.log` is partial (defined as 0 on non-positives). Similarly `Real.sqrt`, `Real.rpow` for negative bases, etc. Many physical-law axioms in this codebase may have hidden hypothesis upgrades waiting to be discovered. A static analyzer pass that flags theorems using these partial functions without corresponding positivity hypotheses would systematize the work of closing more such axioms.

---

## Build state

- **Branch**: `sprint/entropy-axiom-closure-2026-05-25` at commit `076ac0f` (Sprint 1) + this sprint's commit.
- **Build**: 3155 jobs clean, ~7.3s.
- **Sorries**: zero in modified files.
- **Axiom audit**: every newly-closed theorem confirmed at WKL₀ baseline by `#print axioms` output.

---

## Reproducibility

```powershell
# Verify build
lake build SGC.Foundations.AxiomAudit

# Inspect axiom dependencies for the second law
lake build SGC.Foundations.AxiomAudit 2>&1 | Select-String "entropy_production_nonneg"

# Expected output:
# 'SGC.Thermodynamics.entropy_production_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The WKL₀-baseline claim is **empirically verified by Lean's kernel** every time the audit module compiles.
