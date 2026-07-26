/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.LocalToGlobal

/-!
# Continual Compositional Learning: The Assembly Theorems

This module formalizes the **Continual Compositional Assembly Theorem**
(Artemis program, 2026-07-25):

> Local compatibility + protected prior sections + native composition
> topology ⟹ no forgetting + correct novel recombination.

Building on `SGC.Structure.LocalToGlobal` (unique global sections on ranked
computation graphs), we prove the three stages:

## Stage B — the operator language (`Expr`, `certified_implies_correct`)

A typed expression grammar `e ::= x | c | e₁ + e₂ | e₁ * e₂` over a ring.
The **syntax tree of an expression IS a native computation graph**: vertices
are subexpressions, parents are immediate subterms, rank is term size.
`learnedComputation opA opM` runs *learned* binary operations at the `add`
and `mul` cells.

**Theorem (`certified_implies_correct`)**: if the learned operations are
locally certified (`opA = +` and `opM = *` pointwise — a *finitely
checkable* condition over `ZMod p`), then the unique global section of the
compiled sheaf evaluates **every** well-typed expression correctly:
`σ e = evalRing ρ e` for all `e`.  This upgrades the single-expression
result `(x+y)·z` to systematic compositional generalization *by
construction* — arbitrary depth, zero-shot, no training on composites.

## Stage C — safe extension (`SheafExtends`, `no_forgetting`)

`SheafExtends F F' ι` says the extended model `F'` contains the old model
`F` via `ι` with wiring and operations preserved (edges into old cells come
only from old cells — the noninterference/support condition).

**Theorem (`no_forgetting`)**: for ANY such extension and ANY boundary data,
the unique global section of the extended model restricts *exactly* to the
old section: `σ'(ι v) = σ(v)`.  The old computation is an **invariant** of
the extension — stronger than retained accuracy, and independent of
whatever the new cells compute.  This is the formal continual-learning
theorem; the zero-drift `DualTaskMLP` result is its special case.

## Stage D — continual compositional correctness (capstone)

The legacy `(x+y)·z` composition sheaf **embeds** into the expression
grammar (`compEmbed`), and the embedding is a `SheafExtends` morphism.

**Theorem (`continual_compositional_correct`)**: after installing certified
primitives, (1) the legacy machine's section is preserved cell-by-cell, and
(2) every expression of the grammar is evaluated correctly zero-shot:

`τ (compEmbed v) = compSection v  ∧  τ e = evalRing ρ e`.

Preserved old knowledge + typed native interfaces ⟹ correct new
compositions.  The typed interface of Artemis's item 2 is here the shared
stalk ring `R`: addition produces exactly the residue type multiplication
consumes.  (Heterogeneous stalks with `enc`/`dec` interface maps are a
future refinement.)
-/

namespace SGC.Sheaf

/-! ### Stage B: the operator language -/

/-- The typed expression grammar over `R` with `n` variables:
    `e ::= var i | const c | e₁ + e₂ | e₁ * e₂`. -/
inductive Expr (R : Type*) (n : ℕ) where
  | var : Fin n → Expr R n
  | const : R → Expr R n
  | add : Expr R n → Expr R n → Expr R n
  | mul : Expr R n → Expr R n → Expr R n
deriving DecidableEq

namespace Expr

variable {R : Type*} {n : ℕ}

/-- Term size — the acyclicity rank of the syntax DAG. -/
def size : Expr R n → ℕ
  | var _ => 1
  | const _ => 1
  | add e₁ e₂ => e₁.size + e₂.size + 1
  | mul e₁ e₂ => e₁.size + e₂.size + 1

/-- Immediate subterms — the parent list of the syntax DAG. -/
def parents : Expr R n → List (Expr R n)
  | var _ => []
  | const _ => []
  | add e₁ e₂ => [e₁, e₂]
  | mul e₁ e₂ => [e₁, e₂]

end Expr

variable {R : Type*} [Ring R] {n : ℕ}

/-- **Reference semantics**: standard ring evaluation of an expression. -/
def evalRing (ρ : Fin n → R) : Expr R n → R
  | .var i => ρ i
  | .const c => c
  | .add e₁ e₂ => evalRing ρ e₁ + evalRing ρ e₂
  | .mul e₁ e₂ => evalRing ρ e₁ * evalRing ρ e₂

/-- Boundary data for the expression sheaf: variables read the environment,
    constants read themselves, internal cells carry no boundary data. -/
def exprBoundary (ρ : Fin n → R) : Expr R n → R
  | .var i => ρ i
  | .const c => c
  | .add _ _ => 0
  | .mul _ _ => 0

/-- **Compilation**: the expression grammar as a native computation sheaf
    running *learned* operations `opA` (at `add` cells) and `opM` (at `mul`
    cells).  Vertices are subexpressions; the graph is the syntax DAG. -/
def learnedComputation (opA opM : R → R → R) :
    AlgebraicComputation (Expr R n) R where
  parents := Expr.parents
  rank := Expr.size
  op := fun e l =>
    match e, l with
    | .add _ _, [a, b] => opA a b
    | .mul _ _, [a, b] => opM a b
    | _, _ => 0
  wf := by
    intro v u hu
    cases v <;> simp [Expr.parents] at hu <;>
      rcases hu with rfl | rfl <;> simp [Expr.size] <;> omega

/-- The native compilation: exact ring operations at every cell. -/
abbrev exprComputation : AlgebraicComputation (Expr R n) R :=
  learnedComputation (· + ·) (· * ·)

/-- Reference semantics is a global section of the compiled sheaf whenever
    the learned operations are locally certified. -/
theorem evalRing_isSection {opA opM : R → R → R}
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b)
    (ρ : Fin n → R) :
    IsSection (learnedComputation opA opM) (exprBoundary ρ) (evalRing ρ) := by
  constructor
  · intro e hv
    cases e <;> first | rfl | exact absurd hv (List.cons_ne_nil _ _)
  · intro e hv
    cases e with
    | var i => exact absurd rfl hv
    | const c => exact absurd rfl hv
    | add e₁ e₂ =>
        simpa [learnedComputation, Expr.parents, evalRing]
          using (hA (evalRing ρ e₁) (evalRing ρ e₂)).symm
    | mul e₁ e₂ =>
        simpa [learnedComputation, Expr.parents, evalRing]
          using (hM (evalRing ρ e₁) (evalRing ρ e₂)).symm

/-- **Local certification ⟹ global correctness, for every expression.**

    If the learned cell operations satisfy their local algebraic laws
    (finitely checkable over `ZMod p`), then ANY global section of the
    compiled sheaf evaluates every well-typed expression of the grammar
    correctly — arbitrary depth, no composite-task training.

    This is the Stage-B breakthrough theorem: systematic compositional
    generalization by construction. -/
theorem certified_implies_correct {opA opM : R → R → R}
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b)
    (ρ : Fin n → R) {σ : Expr R n → R}
    (hσ : IsSection (learnedComputation opA opM) (exprBoundary ρ) σ)
    (e : Expr R n) :
    σ e = evalRing ρ e :=
  congrFun (hσ.unique (evalRing_isSection hA hM ρ)) e

/-- **Compiler correctness** for the native compilation: the unique section
    of the syntax-DAG sheaf IS ring evaluation.  `evalSheaf = evalRing`. -/
theorem compiler_correct (ρ : Fin n → R) {σ : Expr R n → R}
    (hσ : IsSection (exprComputation (R := R) (n := n)) (exprBoundary ρ) σ)
    (e : Expr R n) :
    σ e = evalRing ρ e :=
  certified_implies_correct (fun _ _ => rfl) (fun _ _ => rfl) ρ hσ e

/-- The compiled expression sheaf has exactly one global section
    (well-posedness of the grammar semantics). -/
theorem expr_existsUnique [DecidableEq R] (opA opM : R → R → R) (ρ : Fin n → R) :
    ∃! σ : Expr R n → R,
      IsSection (learnedComputation opA opM) (exprBoundary ρ) σ :=
  existsUnique_section _ _

/-! ### Stage C: safe extension and the no-forgetting theorem -/

section StageC

variable {V V' : Type*}

/-- **Safe extension**: `F'` extends `F` along `ι` iff every old cell keeps
    exactly its old wiring (`parents_eq` — in particular, no new edges into
    old cells: the noninterference/support condition) and its old operation
    (`op_eq`).  New cells are unconstrained.  Injectivity of `ι` is not
    required. -/
structure SheafExtends (F : AlgebraicComputation V R)
    (F' : AlgebraicComputation V' R) (ι : V → V') : Prop where
  parents_eq : ∀ v, F'.parents (ι v) = (F.parents v).map ι
  op_eq : ∀ v l, F'.op (ι v) l = F.op v l

/-- Sections of an extension restrict to sections of the old model: the
    projection `π := (· ∘ ι)` maps new global sections to old ones. -/
theorem IsSection.restrict {F : AlgebraicComputation V R}
    {F' : AlgebraicComputation V' R} {ι : V → V'}
    (hext : SheafExtends F F' ι) {b : V → R} {b' : V' → R}
    (hb : ∀ v, b' (ι v) = b v) {σ' : V' → R}
    (hσ' : IsSection F' b' σ') : IsSection F b (σ' ∘ ι) := by
  constructor
  · intro v hv
    have hp : F'.parents (ι v) = [] := by
      rw [hext.parents_eq v, hv]; rfl
    exact (hσ'.boundary _ hp).trans (hb v)
  · intro v hv
    have hp : F'.parents (ι v) ≠ [] := by
      rw [hext.parents_eq v]
      intro hnil
      exact hv (List.map_eq_nil_iff.mp hnil)
    calc σ' (ι v)
        = F'.op (ι v) ((F'.parents (ι v)).map σ') := hσ'.local_law _ hp
      _ = F'.op (ι v) (((F.parents v).map ι).map σ') := by rw [hext.parents_eq v]
      _ = F'.op (ι v) ((F.parents v).map (σ' ∘ ι)) := by rw [List.map_map]
      _ = F.op v ((F.parents v).map (σ' ∘ ι)) := hext.op_eq v _

/-- **The No-Forgetting Theorem** (formal continual learning).

    For ANY safe extension of the model and ANY boundary data extending the
    old data, the global section of the extended model agrees with the old
    section on every old cell:

    `π (σ_{t+1} (b_t)) = σ_t (b_t)`.

    The old computation is an *invariant* of the extension — regardless of
    what the new cells compute or how they were trained.  Zero drift on
    protected cells ⟹ zero functional change, as mathematics rather than
    as an empirical report. -/
theorem no_forgetting {F : AlgebraicComputation V R}
    {F' : AlgebraicComputation V' R} {ι : V → V'}
    (hext : SheafExtends F F' ι) {b : V → R} {b' : V' → R}
    (hb : ∀ v, b' (ι v) = b v) {σ : V → R} {σ' : V' → R}
    (hσ : IsSection F b σ) (hσ' : IsSection F' b' σ') :
    ∀ v, σ' (ι v) = σ v :=
  fun v => congrFun ((hσ'.restrict hext hb).unique hσ) v

end StageC

/-! ### Stage D: the legacy machine lives inside the grammar -/

/-- The embedding of the legacy `(x+y)·z` composition graph into the
    expression grammar: each cell maps to the subexpression it computes. -/
def compEmbed {R : Type*} : CompNode → Expr R 3
  | CompNode.X => Expr.var 0
  | CompNode.Y => Expr.var 1
  | CompNode.Z => Expr.var 2
  | CompNode.Sum => Expr.add (Expr.var 0) (Expr.var 1)
  | CompNode.Result => Expr.mul (Expr.add (Expr.var 0) (Expr.var 1)) (Expr.var 2)

/-- The legacy composition sheaf (identity restrictions) extends to the
    certified expression sheaf along `compEmbed`: wiring and operations are
    preserved cell-by-cell. -/
theorem compEmbed_extends (Fc : CellularSheaf CompositionGraph R)
    (hid : ∀ e a, Fc.restriction e a = a)
    {opA opM : R → R → R}
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b) :
    SheafExtends (sheafComputation Fc) (learnedComputation opA opM) compEmbed := by
  constructor
  · intro v
    cases v <;> rfl
  · intro v l
    cases v <;>
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
        simp [learnedComputation, sheafComputation, compEmbed, hid, hA, hM]

/-- The expression boundary restricts to the legacy boundary. -/
theorem compEmbed_boundary (ρ : Fin 3 → R) (v : CompNode) :
    exprBoundary ρ (compEmbed v) = compBoundary (ρ 0) (ρ 1) (ρ 2) v := by
  cases v <;> rfl

/-- **Legacy preservation**: any global section of the certified expression
    sheaf agrees, on the image of the legacy machine, with the legacy
    section — the old `(x+y)·z` computation runs unchanged inside the
    grammar. -/
theorem legacy_section_preserved (Fc : CellularSheaf CompositionGraph R)
    (hid : ∀ e a, Fc.restriction e a = a)
    {opA opM : R → R → R}
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b)
    (ρ : Fin 3 → R) {τ : Expr R 3 → R}
    (hτ : IsSection (learnedComputation opA opM) (exprBoundary ρ) τ)
    (v : CompNode) :
    τ (compEmbed v) = compSection Fc (ρ 0) (ρ 1) (ρ 2) v :=
  no_forgetting (compEmbed_extends Fc hid hA hM) (compEmbed_boundary ρ)
    (compSection_isSection Fc _ _ _) hτ v

/-- **The Continual Compositional Assembly Theorem** (Stage D capstone).

    Suppose the primitives are installed as certified cells (`hA`, `hM`)
    of the native expression sheaf.  Then, for the unique global section
    `τ` of the extended model:

    1. **No forgetting** — the legacy `(x+y)·z` machine's section is
       preserved cell-by-cell: `τ (compEmbed v) = compSection v`; and
    2. **Correct novel recombination** — every well-typed expression of the
       grammar is evaluated correctly, zero-shot:
       `τ e = evalRing ρ e` for ALL `e` (in particular `x(y+z)`,
       `(x+y)(z+w)`, `(x+y)z + w`, and every deeper tree).

    Local compatibility + protected prior sections + native composition
    topology ⟹ no forgetting + correct novel recombination. -/
theorem continual_compositional_correct (Fc : CellularSheaf CompositionGraph R)
    (hid : ∀ e a, Fc.restriction e a = a)
    {opA opM : R → R → R}
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b)
    (ρ : Fin 3 → R) {τ : Expr R 3 → R}
    (hτ : IsSection (learnedComputation opA opM) (exprBoundary ρ) τ) :
    (∀ v : CompNode, τ (compEmbed v) = compSection Fc (ρ 0) (ρ 1) (ρ 2) v) ∧
    (∀ e : Expr R 3, τ e = evalRing ρ e) :=
  ⟨legacy_section_preserved Fc hid hA hM ρ hτ,
   fun e => certified_implies_correct hA hM ρ hτ e⟩

end SGC.Sheaf
