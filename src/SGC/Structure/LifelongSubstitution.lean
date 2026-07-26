/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.ContinualComposition

/-!
# Certified Lifelong Substitution

This module completes the exact theorem ladder for compositional continual
learning (Artemis program, second directive, 2026-07-25):

> **Certified + SafeExtension\* + WellTypedSubstitution ⟹
>   Preservation + ExactComposition.**

## The theorem ladder

* **Ladder 3 (done previously)** — `no_forgetting`: one safe extension
  preserves the old section exactly.

* **Ladder 4 (`lifelong_no_forgetting`)** — safe extensions form a
  *category*: `SheafExtends.refl` and `SheafExtends.comp` show identity and
  closure under composition, `extends_embedUpTo` composes an arbitrary
  finite chain `F₀ ↪ F₁ ↪ ⋯ ↪ Fₙ`, and the lifelong theorem concludes
  `σₙ(i₀ₙ(v)) = σ₀(v)`: **any finite sequence of certified safe additions
  preserves every protected computation.**

* **Ladder 5 (`evalRing_subst`, `section_subst`)** — the substitution
  theorem, the categorical heart of composition.  Syntactic substitution
  `e[θ]` commutes with evaluation, and at the sheaf level: grafting a
  learned subprogram at a variable site preserves the intended global
  semantics — the section of the grafted graph is computed by the section
  of the outer graph run on the sections of the inner graphs.

* **Capstone (`certified_lifelong_substitution`)** — in a chain of safe
  extensions of certified computation sheaves, every formerly certified
  subcomputation remains semantically invariant, and any well-typed
  expression formed by substitution from the accumulated certified
  primitives evaluates to its denotational semantics.

## The organizing object

`CertifiedOps R` packages learned operations together with their local
certificates (`op = ⟦symbol⟧` pointwise), making the add/mul certificate a
special case of the signature-level design.  `CertifiedOps.native` witnesses
inhabitation.  We deliberately do *not* call the compiled object a standard
cellular sheaf: it carries vertex stalks, ranked dependencies, and local
operations, but not yet the conventional edge-stalk/coboundary data (that
connection — via Bosca–Ghrist harmonic extension — is future work).
-/

namespace SGC.Sheaf

variable {R : Type*}

/-! ### Ladder 4a: safe extensions form a category -/

/-- The identity extension: every model safely extends itself. -/
theorem SheafExtends.refl {V : Type*} (F : AlgebraicComputation V R) :
    SheafExtends F F id :=
  ⟨fun v => (List.map_id _).symm, fun _ _ => rfl⟩

/-- **Safe extensions compose**: extending an extension is an extension.
    This is closure of the certified-update discipline under iteration. -/
theorem SheafExtends.comp {V V' V'' : Type*}
    {F : AlgebraicComputation V R} {G : AlgebraicComputation V' R}
    {H : AlgebraicComputation V'' R} {ι : V → V'} {κ : V' → V''}
    (h₁ : SheafExtends F G ι) (h₂ : SheafExtends G H κ) :
    SheafExtends F H (κ ∘ ι) := by
  constructor
  · intro v
    show H.parents (κ (ι v)) = _
    rw [h₂.parents_eq, h₁.parents_eq, List.map_map]
  · intro v l
    show H.op (κ (ι v)) l = _
    rw [h₂.op_eq, h₁.op_eq]

/-! ### Ladder 4b: finite chains of extensions -/

/-- The composite embedding `i₀ₙ : V₀ → Vₙ` along a chain of extensions. -/
def embedUpTo {V : ℕ → Type*} (ι : ∀ k, V k → V (k + 1)) :
    (n : ℕ) → V 0 → V n
  | 0 => id
  | n + 1 => ι n ∘ embedUpTo ι n

/-- A chain of safe extensions composes to a safe extension `F₀ ↪ Fₙ`. -/
theorem extends_embedUpTo {V : ℕ → Type*}
    {F : ∀ k, AlgebraicComputation (V k) R} {ι : ∀ k, V k → V (k + 1)}
    (hext : ∀ k, SheafExtends (F k) (F (k + 1)) (ι k)) (n : ℕ) :
    SheafExtends (F 0) (F n) (embedUpTo ι n) := by
  induction n with
  | zero => exact SheafExtends.refl _
  | succ n ih => exact ih.comp (hext n)

/-- **The Lifelong Extension Theorem** (ladder 4).

    Along ANY finite chain of safe extensions
    `F₀ ↪ F₁ ↪ ⋯ ↪ Fₙ` with compatible boundary data, the global section
    of the final model agrees with the original section on every protected
    cell:

    `σₙ(i₀ₙ(v)) = σ₀(v)`.

    One safe extension does not forget; a *lifetime* of certified safe
    additions does not forget either. -/
theorem lifelong_no_forgetting {V : ℕ → Type*}
    {F : ∀ k, AlgebraicComputation (V k) R} {ι : ∀ k, V k → V (k + 1)}
    (hext : ∀ k, SheafExtends (F k) (F (k + 1)) (ι k))
    {b : ∀ k, V k → R} (hb : ∀ k v, b (k + 1) (ι k v) = b k v)
    {σ : ∀ k, V k → R} (hσ : ∀ k, IsSection (F k) (b k) (σ k)) :
    ∀ n v, σ n (embedUpTo ι n v) = σ 0 v := by
  intro n v
  have hbn : ∀ w, b n (embedUpTo ι n w) = b 0 w := by
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      exact (hb n (embedUpTo ι n w)).trans (ih w)
  exact no_forgetting (extends_embedUpTo hext n) hbn (hσ 0) (hσ n) v

/-! ### Ladder 5: the substitution theorem -/

namespace Expr

variable {n m : ℕ}

/-- Substitution: replace each variable of `e` by an expression.
    This is grafting of syntax trees. -/
def subst (θ : Fin n → Expr R m) : Expr R n → Expr R m
  | var i => θ i
  | const c => const c
  | add e₁ e₂ => add (e₁.subst θ) (e₂.subst θ)
  | mul e₁ e₂ => mul (e₁.subst θ) (e₂.subst θ)

end Expr

variable [Ring R] {n m : ℕ}

/-- **The Substitution Theorem** (syntactic level): evaluation commutes
    with substitution.

    `eval(e[θ], ρ) = eval(e, i ↦ eval(θ(i), ρ))`. -/
theorem evalRing_subst (θ : Fin n → Expr R m) (ρ : Fin m → R)
    (e : Expr R n) :
    evalRing ρ (e.subst θ) = evalRing (fun i => evalRing ρ (θ i)) e := by
  induction e with
  | var i => rfl
  | const c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp [Expr.subst, evalRing, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [Expr.subst, evalRing, ih₁, ih₂]

/-- **The Substitution Theorem** (sheaf level): compilation respects
    grafting.

    Let `σ` be the global section of the certified sheaf over environment
    `ρ`, and let `τ` be the global section over the environment that reads
    the sections of the subprograms `θ i`.  Then evaluating a grafted
    expression with `σ` equals evaluating the outer expression with `τ`:

    `σ(e[θ]) = τ(e)`.

    Adding a learned subprogram at a variable site preserves the intended
    global semantics — the categorical heart of composition. -/
theorem section_subst {opA opM : R → R → R}
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b)
    (θ : Fin n → Expr R m) (ρ : Fin m → R)
    {σ : Expr R m → R}
    (hσ : IsSection (learnedComputation opA opM) (exprBoundary ρ) σ)
    {τ : Expr R n → R}
    (hτ : IsSection (learnedComputation opA opM)
      (exprBoundary fun i => σ (θ i)) τ)
    (e : Expr R n) :
    σ (e.subst θ) = τ e := by
  have hθ : (fun i => σ (θ i)) = fun i => evalRing ρ (θ i) := by
    funext i
    exact certified_implies_correct hA hM ρ hσ (θ i)
  rw [certified_implies_correct hA hM ρ hσ (e.subst θ), evalRing_subst,
    certified_implies_correct hA hM _ hτ e, hθ]

/-! ### The organizing object: certified operations -/

/-- **Certified operations**: learned binary operations packaged with their
    local certificates `op = ⟦symbol⟧`.  Over `ZMod p` the certificates are
    finitely checkable; here they are carried as proof obligations.  This
    is the signature-level object of which the ad hoc `hA`/`hM` hypotheses
    were special cases. -/
structure CertifiedOps (R : Type*) [Ring R] where
  /-- The learned addition cell. -/
  opA : R → R → R
  /-- The learned multiplication cell. -/
  opM : R → R → R
  /-- Local certificate: the addition cell satisfies its algebraic law. -/
  certA : ∀ a b, opA a b = a + b
  /-- Local certificate: the multiplication cell satisfies its law. -/
  certM : ∀ a b, opM a b = a * b

/-- The exact native operations are certified (inhabitation witness). -/
def CertifiedOps.native (R : Type*) [Ring R] : CertifiedOps R :=
  ⟨(· + ·), (· * ·), fun _ _ => rfl, fun _ _ => rfl⟩

/-- The computation sheaf compiled from certified operations. -/
def CertifiedOps.computation (C : CertifiedOps R) {n : ℕ} :
    AlgebraicComputation (Expr R n) R :=
  learnedComputation C.opA C.opM

/-! ### The capstone -/

/-- **Theorem — Certified Lifelong Substitution.**

    In a chain of safe extensions of certified algebraic computation
    sheaves:

    1. **Preservation** — every formerly certified subcomputation remains
       semantically invariant across the whole chain:
       `σₙ(i₀ₙ(v)) = σ₀(v)`; and
    2. **Exact composition** — any well-typed expression formed by
       substitution from the accumulated certified primitives evaluates to
       its denotational semantics:
       `τ(e[θ]) = eval(e, i ↦ eval(θ(i), ρ))`.

    In compressed form:

    `Certified + SafeExtension* + WellTypedSubstitution ⟹
     Preservation + ExactComposition.`

    This is the formal statement of compositional continual learning,
    with no unproven assertions about SGD, latent representations, or
    noise-driven grokking. -/
theorem certified_lifelong_substitution
    -- a lifetime of safe extensions
    {V : ℕ → Type*} {F : ∀ k, AlgebraicComputation (V k) R}
    {ι : ∀ k, V k → V (k + 1)}
    (hext : ∀ k, SheafExtends (F k) (F (k + 1)) (ι k))
    {b : ∀ k, V k → R} (hb : ∀ k v, b (k + 1) (ι k v) = b k v)
    {σ : ∀ k, V k → R} (hσ : ∀ k, IsSection (F k) (b k) (σ k))
    -- accumulated certified primitives, substitution, environment
    (C : CertifiedOps R) (θ : Fin n → Expr R m) (ρ : Fin m → R)
    {τ : Expr R m → R}
    (hτ : IsSection (C.computation) (exprBoundary ρ) τ) :
    (∀ k v, σ k (embedUpTo ι k v) = σ 0 v) ∧
    (∀ e : Expr R n,
      τ (e.subst θ) = evalRing (fun i => evalRing ρ (θ i)) e) := by
  refine ⟨lifelong_no_forgetting hext hb hσ, fun e => ?_⟩
  rw [certified_implies_correct C.certA C.certM ρ hτ (e.subst θ),
    evalRing_subst]

end SGC.Sheaf
