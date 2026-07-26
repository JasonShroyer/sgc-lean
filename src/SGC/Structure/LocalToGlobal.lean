/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.CellularSheaf
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic

/-!
# Local-to-Global Computation: The Native Sheaf Theorems

This module proves the theorems that were previously placeholders in
`SGC.Structure.CellularSheaf`, connecting the SGC cellular-sheaf architecture
to the Bosca–Ghrist local-to-global framework ("Neural Networks as
Local-to-Global Computation").

## The five theorems

1. **`existsUnique_section`** (Local-to-Global): a finite acyclic computation
   graph with a local operation at each internal vertex admits a *unique*
   global section extending any boundary data.  Existence is topological
   evaluation (`eval`); uniqueness is strong induction on rank.  This is the
   deterministic core of the Bosca–Ghrist harmonic-extension theorem.

2. **`sheaf_assembly`** (Assembly): if the restriction maps of a cellular
   sheaf on the composition graph are ring homomorphisms coherent along
   paths, the unique compatible section satisfies
   `σ(Result) = ψ(φ((x + y) * z))` — the network *is* a realization of the
   polynomial `(x+y)·z` under the path homomorphism.  This replaces the
   former placeholder axiom `sheaf_assembly_theorem`.

3. **`no_separable_composition`** (Impossibility): over ANY nontrivial ring
   there are NO unary maps `f g h` with `f a + g b + h z = (a+b)·z`.
   Since the star-connector energy minimizer is the arithmetic mean of unary
   images (`starEnergy_argmin`), post-hoc energy gluing computes a separable
   function and therefore *cannot* compute the composite task
   (`starConnector_cannot_compose`).  This is the 3.4% Sheaf-Connector
   failure, promoted to a theorem.

4. **`defect_propagation`** (Approximate assembly): local defects compose
   linearly with depth — `|out - (x+y)z| ≤ δ₂ + δ₁·|z|`.  This is the
   quantitative bridge from `FunctorialDefectBound` to global correctness.

5. **`grokked_iff_defect_zero` / `native_defect_zero`** (Grokking):
   on a finite dataset the compositional defect vanishes iff the global law
   is exact, and the native sheaf (identity restrictions) has defect zero on
   *every* dataset.  Grokking is the transition to the zero-defect regime.

## Slogan

> Once the computation graph itself carries the task algebra, local
> compatibility determines the global computation (T1, T2).  Consensus
> dynamics without the algebra provably cannot (T3).  Defects measure the
> distance to the exact regime (T4), and grokking is the crossing (T5).
-/

namespace SGC.Sheaf

/-! ### 1. Algebraic computation graphs -/

/-- An **algebraic computation graph**: each vertex has an ordered list of
    parents, a local operation combining parent values, and a rank function
    certifying acyclicity (every parent has strictly smaller rank).

    Vertices with no parents are *boundary* (input) vertices. -/
structure AlgebraicComputation (V : Type*) (R : Type*) where
  /-- Ordered list of parents (in-neighbors) of each vertex. -/
  parents : V → List V
  /-- Local operation at each vertex, applied to parent values in order. -/
  op : V → List R → R
  /-- Rank certifying acyclicity. -/
  rank : V → ℕ
  /-- Every parent has strictly smaller rank. -/
  wf : ∀ v u, u ∈ parents v → rank u < rank v

variable {V : Type*} {R : Type*}

/-- A **global section** for boundary data `b`: agrees with `b` on boundary
    vertices and satisfies the local computation law at every internal
    vertex.  This is the sheaf-section / harmonic-extension compatibility
    condition in the deterministic setting. -/
structure IsSection (C : AlgebraicComputation V R) (b : V → R) (σ : V → R) : Prop where
  boundary : ∀ v, C.parents v = [] → σ v = b v
  local_law : ∀ v, C.parents v ≠ [] → σ v = C.op v ((C.parents v).map σ)

/-- **Topological evaluation**: the canonical global section, defined by
    well-founded recursion on rank.  This is the "forward pass". -/
def eval (C : AlgebraicComputation V R) (b : V → R) (v : V) : R :=
  if h : C.parents v = [] then b v
  else C.op v ((C.parents v).pmap (fun u hu => eval C b u) (fun _ hu => hu))
termination_by C.rank v
decreasing_by exact C.wf v u hu

/-- Unfolding lemma for `eval`. -/
theorem eval_eq (C : AlgebraicComputation V R) (b : V → R) (v : V) :
    eval C b v = if C.parents v = [] then b v
      else C.op v ((C.parents v).map (eval C b)) := by
  rw [eval]
  by_cases h : C.parents v = []
  · simp [h]
  · simp [h, List.pmap_eq_map]

/-- Mapping two functions that agree on the members of a list gives the
    same result. -/
private theorem map_congr_mem {α β : Type*} {l : List α} {f g : α → β}
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- **Existence**: the forward pass is a global section. -/
theorem eval_isSection (C : AlgebraicComputation V R) (b : V → R) :
    IsSection C b (eval C b) := by
  constructor
  · intro v hv
    rw [eval_eq, if_pos hv]
  · intro v hv
    rw [eval_eq, if_neg hv]

/-- **Uniqueness**: any two global sections for the same boundary data are
    equal.  Proof: strong induction on rank — local laws propagate agreement
    from the boundary upward. -/
theorem IsSection.unique {C : AlgebraicComputation V R} {b : V → R} {σ τ : V → R}
    (hσ : IsSection C b σ) (hτ : IsSection C b τ) : σ = τ := by
  funext v
  suffices H : ∀ n, ∀ w : V, C.rank w ≤ n → σ w = τ w from H (C.rank v) v le_rfl
  intro n
  induction n with
  | zero =>
    intro w hw
    rcases eq_or_ne (C.parents w) [] with h | h
    · rw [hσ.boundary w h, hτ.boundary w h]
    · obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ h
      exact absurd (C.wf w u hu) (by omega)
  | succ n ih =>
    intro w hw
    rcases eq_or_ne (C.parents w) [] with h | h
    · rw [hσ.boundary w h, hτ.boundary w h]
    · rw [hσ.local_law w h, hτ.local_law w h]
      exact congrArg (C.op w)
        (map_congr_mem fun u hu => ih u (by have := C.wf w u hu; omega))

/-- **T1. Local-to-Global Computation Theorem**: a finite acyclic
    computation graph admits exactly one global section extending any
    boundary data.  Local compatibility determines the global computation. -/
theorem existsUnique_section (C : AlgebraicComputation V R) (b : V → R) :
    ∃! σ : V → R, IsSection C b σ :=
  ⟨eval C b, eval_isSection C b, fun _ hτ => hτ.unique (eval_isSection C b)⟩

/-! ### 2. The composition graph as an algebraic computation

We now instantiate the general theory on the 5-node graph for `(x+y)·z`
from `SGC.Structure.CellularSheaf`, with the sheaf restriction maps woven
into the local operations (messages are restricted, then aggregated
according to `compAggregation`: `Sum` at the `Sum` node, `Product` at the
`Result` node). -/

/-- Parents of each node of the composition graph, in evaluation order. -/
def compParents : CompNode → List CompNode
  | CompNode.X => []
  | CompNode.Y => []
  | CompNode.Z => []
  | CompNode.Sum => [CompNode.X, CompNode.Y]
  | CompNode.Result => [CompNode.Sum, CompNode.Z]

/-- Topological rank of each node. -/
def compRank : CompNode → ℕ
  | CompNode.X => 0
  | CompNode.Y => 0
  | CompNode.Z => 0
  | CompNode.Sum => 1
  | CompNode.Result => 2

variable [Ring R]

/-- The algebraic computation induced by a cellular sheaf on the composition
    graph: restrict incoming messages along edges, then aggregate additively
    at `Sum` and multiplicatively at `Result` (the `compAggregation`
    semantics). -/
def sheafComputation (F : CellularSheaf CompositionGraph R) :
    AlgebraicComputation CompNode R where
  parents := compParents
  rank := compRank
  op := fun v l =>
    match v, l with
    | CompNode.Sum, [a, b] =>
        F.restriction (CompNode.X, CompNode.Sum) a +
        F.restriction (CompNode.Y, CompNode.Sum) b
    | CompNode.Result, [s, z] =>
        F.restriction (CompNode.Sum, CompNode.Result) s *
        F.restriction (CompNode.Z, CompNode.Result) z
    | _, _ => 0
  wf := by decide

/-- Boundary data placing `x, y, z` on the input nodes. -/
def compBoundary (x y z : R) : CompNode → R
  | CompNode.X => x
  | CompNode.Y => y
  | CompNode.Z => z
  | _ => 0

/-- The explicit global section of the composition sheaf. -/
def compSection (F : CellularSheaf CompositionGraph R) (x y z : R) : CompNode → R
  | CompNode.X => x
  | CompNode.Y => y
  | CompNode.Z => z
  | CompNode.Sum =>
      F.restriction (CompNode.X, CompNode.Sum) x +
      F.restriction (CompNode.Y, CompNode.Sum) y
  | CompNode.Result =>
      F.restriction (CompNode.Sum, CompNode.Result)
        (F.restriction (CompNode.X, CompNode.Sum) x +
         F.restriction (CompNode.Y, CompNode.Sum) y) *
      F.restriction (CompNode.Z, CompNode.Result) z

/-- `compSection` is a global section. -/
theorem compSection_isSection (F : CellularSheaf CompositionGraph R) (x y z : R) :
    IsSection (sheafComputation F) (compBoundary x y z) (compSection F x y z) := by
  constructor
  · intro v hv
    cases v <;> first | rfl | exact absurd hv (by decide)
  · intro v hv
    cases v <;> first | rfl | exact absurd rfl hv

/-- The composition sheaf has exactly one global section for each input. -/
theorem native_existsUnique (F : CellularSheaf CompositionGraph R) (x y z : R) :
    ∃! σ : CompNode → R, IsSection (sheafComputation F) (compBoundary x y z) σ :=
  existsUnique_section _ _

/-- **T2. Sheaf Assembly Theorem** (proved — replaces the former placeholder
    axiom `sheaf_assembly_theorem`).

    If the restriction maps of the cellular sheaf are ring homomorphisms
    that cohere along paths (`Z → Result` carries the composite `ψ ∘ φ`),
    then the *unique* global section realizes the polynomial `(x+y)·z`
    under the path homomorphism:

    `σ(Result) = ψ(φ((x + y) * z))`.

    Grokking, in the exact regime, IS the emergence of this homomorphism:
    the network becomes a realization of `ℤₚ[x,y,z] → R` on the task
    polynomial. -/
theorem sheaf_assembly (F : CellularSheaf CompositionGraph R) (φ ψ : R →+* R)
    (hXS : ∀ a, F.restriction (CompNode.X, CompNode.Sum) a = φ a)
    (hYS : ∀ a, F.restriction (CompNode.Y, CompNode.Sum) a = φ a)
    (hSR : ∀ a, F.restriction (CompNode.Sum, CompNode.Result) a = ψ a)
    (hZR : ∀ a, F.restriction (CompNode.Z, CompNode.Result) a = ψ (φ a))
    (x y z : R) (σ : CompNode → R)
    (hσ : IsSection (sheafComputation F) (compBoundary x y z) σ) :
    σ CompNode.Result = ψ (φ ((x + y) * z)) := by
  have hσc : σ = compSection F x y z := hσ.unique (compSection_isSection F x y z)
  rw [hσc]
  show F.restriction (CompNode.Sum, CompNode.Result)
      (F.restriction (CompNode.X, CompNode.Sum) x +
       F.restriction (CompNode.Y, CompNode.Sum) y) *
      F.restriction (CompNode.Z, CompNode.Result) z = ψ (φ ((x + y) * z))
  rw [hXS, hYS, hSR, hZR, ← map_add φ, ← map_mul ψ, ← map_mul φ]

/-- **Corollary**: with identity restrictions the native sheaf computes the
    task *exactly*: every compatible global section outputs `(x+y)·z`.
    Compositional generalization is structural, not statistical. -/
theorem native_sheaf_computes (F : CellularSheaf CompositionGraph R)
    (hid : ∀ e a, F.restriction e a = a)
    (x y z : R) (σ : CompNode → R)
    (hσ : IsSection (sheafComputation F) (compBoundary x y z) σ) :
    σ CompNode.Result = (x + y) * z := by
  have h := sheaf_assembly F (RingHom.id R) (RingHom.id R)
    (fun a => hid _ a) (fun a => hid _ a) (fun a => hid _ a) (fun a => hid _ a)
    x y z σ hσ
  simpa using h

/-! ### 3. The impossibility theorem: diffusion is not composition

The failed "Sheaf Connector" (3.4% accuracy) glued three frozen unary
representations by minimizing a star-shaped disagreement energy.  Its
equilibrium is the arithmetic mean of the three unary images — an
*additively separable* function of the inputs.  We prove that NO separable
function equals `(a+b)·z`, over any nontrivial ring.  Hence energy-only
gluing can never compute the composite, no matter what unary maps are
learned.  The failure was structural, not a training deficiency. -/

/-- **T3a. Non-separability of composition**: over any nontrivial ring there
    are no unary maps `f, g, h` with `f a + g b + h z = (a + b) * z` for all
    inputs.  The composite task is not additively separable. -/
theorem no_separable_composition (R : Type*) [Ring R] [Nontrivial R] :
    ¬ ∃ f g h : R → R, ∀ a b z : R, f a + g b + h z = (a + b) * z := by
  rintro ⟨f, g, h, H⟩
  have h1 : f 0 + g 0 + h 0 = 0 := by simpa using H 0 0 0
  have h2 : f 0 + g 0 + h 1 = 0 := by simpa using H 0 0 1
  have h3 : f 1 + g 0 + h 0 = 0 := by simpa using H 1 0 0
  have h4 : f 1 + g 0 + h 1 = 1 := by simpa using H 1 0 1
  have hh : h 0 = h 1 := add_left_cancel (h1.trans h2.symm)
  rw [hh] at h3
  exact one_ne_zero (h4.symm.trans h3)

/-- The star-connector disagreement energy: squared distance of the latent
    consensus `c` from the three projected representations. -/
def starEnergy (p q r c : ℝ) : ℝ := (p - c) ^ 2 + (q - c) ^ 2 + (r - c) ^ 2

/-- The arithmetic mean minimizes the star energy. -/
theorem starEnergy_min (p q r c : ℝ) :
    starEnergy p q r ((p + q + r) / 3) ≤ starEnergy p q r c := by
  unfold starEnergy
  nlinarith [sq_nonneg (c - (p + q + r) / 3)]

/-- **Harmonic consensus**: any minimizer of the star energy IS the
    arithmetic mean — sheaf diffusion on the star graph computes averaging,
    nothing else. -/
theorem starEnergy_argmin (p q r c : ℝ)
    (hmin : ∀ c', starEnergy p q r c ≤ starEnergy p q r c') :
    c = (p + q + r) / 3 := by
  have h1 := hmin ((p + q + r) / 3)
  have h2 : (c - (p + q + r) / 3) ^ 2 ≤ 0 := by
    unfold starEnergy at h1
    nlinarith
  have h3 : (c - (p + q + r) / 3) ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
  have h4 : (c - (p + q + r) / 3) * (c - (p + q + r) / 3) = 0 := by
    linear_combination h3
  have h5 := mul_self_eq_zero.mp h4
  linarith [h5]

/-- Energy-only gluing computes a separable equilibrium, so it cannot equal
    the composite on all inputs. -/
theorem energy_gluing_cannot_compose (ρA ρB ρZ : ℝ → ℝ) :
    ¬ ∀ a b z : ℝ, (ρA a + ρB b + ρZ z) / 3 = (a + b) * z := by
  intro H
  apply no_separable_composition ℝ
  refine ⟨fun a => ρA a / 3, fun b => ρB b / 3, fun z => ρZ z / 3, fun a b z => ?_⟩
  linarith [H a b z]

/-- **T3b. The Sheaf-Connector Impossibility Theorem**: for ANY learned
    unary restriction maps `ρA, ρB, ρZ`, there exist inputs on which the
    unique star-energy minimizer differs from the composite `(a+b)·z`.

    Post-hoc gluing of frozen representations by disagreement minimization
    is structurally incapable of composition — the formal content of the
    3.4% experiment. -/
theorem starConnector_cannot_compose (ρA ρB ρZ : ℝ → ℝ) :
    ∃ a b z : ℝ, ∀ c : ℝ,
      (∀ c', starEnergy (ρA a) (ρB b) (ρZ z) c ≤ starEnergy (ρA a) (ρB b) (ρZ z) c') →
      c ≠ (a + b) * z := by
  by_contra hcon
  push_neg at hcon
  apply energy_gluing_cannot_compose ρA ρB ρZ
  intro a b z
  obtain ⟨c, hc_min, hc_eq⟩ := hcon a b z
  have hc := starEnergy_argmin _ _ _ _ hc_min
  rw [← hc, hc_eq]

/-! ### 4. Defect propagation: the approximate assembly theorem

When the learned local operations are only δ-close to the task algebra,
the global compositional error is controlled *linearly* by the local
defects, weighted by the downstream multiplier.  This is the quantitative
content of `FunctorialDefectBound`: small local defects ⇒ small global
defect, uniformly over inputs. -/

/-- **T4. Defect Propagation Theorem**: if the learned sum operation has
    defect `δ₁` and the learned product operation has defect `δ₂`, the
    end-to-end compositional defect is at most `δ₂ + δ₁·|z|`.
    Local consistency bounds global error — the ε-δ version of the
    assembly theorem. -/
theorem defect_propagation (opS opR : ℝ → ℝ → ℝ) (δ₁ δ₂ : ℝ)
    (hS : ∀ x y : ℝ, |opS x y - (x + y)| ≤ δ₁)
    (hR : ∀ s z : ℝ, |opR s z - s * z| ≤ δ₂)
    (x y z : ℝ) :
    |opR (opS x y) z - (x + y) * z| ≤ δ₂ + δ₁ * |z| := by
  have key : opR (opS x y) z - (x + y) * z =
      (opR (opS x y) z - opS x y * z) + (opS x y - (x + y)) * z := by ring
  rw [key]
  calc |(opR (opS x y) z - opS x y * z) + (opS x y - (x + y)) * z|
      ≤ |opR (opS x y) z - opS x y * z| + |(opS x y - (x + y)) * z| := abs_add _ _
    _ ≤ δ₂ + δ₁ * |z| := by
        rw [abs_mul]
        exact add_le_add (hR _ _)
          (mul_le_mul_of_nonneg_right (hS x y) (abs_nonneg z))

/-! ### 5. Grokking as the zero-defect transition

On a finite dataset the compositional defect is a mismatch count.  Grokking
— in the exact, mathematical sense — is the event that this count reaches
zero.  The native sheaf achieves it structurally, on every dataset. -/

/-- The **compositional defect** of an output map on a finite dataset:
    the number of triples where the map disagrees with `(x+y)·z`. -/
def compositionalDefect {R : Type*} [Ring R] [DecidableEq R]
    (D : Finset (R × R × R)) (out : R → R → R → R) : ℕ :=
  (D.filter fun t => out t.1 t.2.1 t.2.2 ≠ (t.1 + t.2.1) * t.2.2).card

/-- **T5a. Grokking criterion**: the compositional defect vanishes iff the
    global law is exact on the dataset.  Grokking is the crossing into the
    zero-defect regime — thresholds like `ε < 0.15` are detector settings,
    this is the mathematical event they detect. -/
theorem grokked_iff_defect_zero {R : Type*} [Ring R] [DecidableEq R]
    (D : Finset (R × R × R)) (out : R → R → R → R) :
    compositionalDefect D out = 0 ↔
      ∀ t ∈ D, out t.1 t.2.1 t.2.2 = (t.1 + t.2.1) * t.2.2 := by
  simp [compositionalDefect, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- The output of the native sheaf: the `Result` coordinate of its unique
    global section. -/
def sheafOutput (F : CellularSheaf CompositionGraph R) (x y z : R) : R :=
  compSection F x y z CompNode.Result

/-- **T5b. The native sheaf groks structurally**: with identity restrictions
    its compositional defect is zero on EVERY dataset.  Combined with
    `starConnector_cannot_compose`, this is the complete formal account of
    the experimental record: native = 100%, retrofitted = chance. -/
theorem native_defect_zero {R : Type*} [Ring R] [DecidableEq R]
    (F : CellularSheaf CompositionGraph R)
    (hid : ∀ e a, F.restriction e a = a)
    (D : Finset (R × R × R)) :
    compositionalDefect D (sheafOutput F) = 0 := by
  rw [grokked_iff_defect_zero]
  intro t _
  simp [sheafOutput, compSection, hid]

end SGC.Sheaf
