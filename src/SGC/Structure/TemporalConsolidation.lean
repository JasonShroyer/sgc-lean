/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Structure.LifelongSubstitution
import SGC.Structure.ErrorBudget

/-!
# The Certified Consolidation Theorem

A temporal, continually learning system with the decisive separation:

`A_t` (plastic, exploratory, self-tuning)  ≠  `M_t` (certified, protected,
compositional).

## The formal design

* **`MemoryState`** — protected memory `M_t`: a computation graph, boundary
  data, and the *stored global section* (the durable knowledge content),
  bundled with the proof that the stored values really are the section.

* **`TemporalState`** — `M_t` paired with an active state `A_t : α` for an
  ARBITRARY type `α`.  Attention scores, thresholds, priors, provisional
  graphs, novelty signals — all live inside `α`.

* **`Consolidation`** — the ONLY channel that changes memory: a safe
  extension (`SheafExtends`) with matching boundary data.  Retention is
  the identity consolidation (`Consolidation.retain`); consolidations
  compose (`Consolidation.comp`).

* **`TemporalStep`** — one tick of the system: memory consolidates safely;
  the active component is *unconstrained* — there is literally no field
  restricting it.  **The protection condition holds by construction**: the
  API contains no channel by which activity, attention, or any policy can
  mutate stored memory; policies may freely *read* memory (any function of
  the state may drive `α`'s evolution) but may change `M_t` only through
  certified consolidation.

## The theorems

1. **`Consolidation.preserves`** — one consolidation step preserves every
   stored value (reuses `no_forgetting`).
2. **`lifelong_consolidation`** — along ANY trajectory, all stored memory
   is invariant for all time (reuses `lifelong_no_forgetting`).
3. **`OpsLibrary.step` / `OpsLibrary.upTo`** — an installed operator
   library persists through consolidation: the certified vocabulary is
   monotone (capability growth without loss).
4. **`temporal_exact_composition`** — certified memory ⟹ exact
   composition of every well-typed expression, at every time.
5. **`temporal_bounded_composition`** — defect-bounded memory ⟹
   error-budgeted composition at every time (the approximate branch).
6. **`certified_consolidation`** — the capstone conjunction:
   no forgetting + exact composition, forever.
7. **`plastic_system_correct`** — such a system EXISTS: a concrete witness
   whose active state follows an arbitrary evolution `a : ℕ → α` while
   every expression evaluates exactly, at every time.

The theorem-level invariant, as requested:

> Plasticity may change `A_t`; only certified safe extension may change
> `M_t`.

Adaptive attention (`π_t`) and coherence descent (`E(A_{t+1}) ≤ E(A_t)`)
are deliberately NOT formalized here — the consolidation boundary makes
whatever policy is chosen later safe by construction.
-/

namespace SGC.Sheaf

variable {R : Type*}

/-! ### Protected memory and consolidation -/

/-- **Protected memory** `M_t`: a computation graph with boundary data and
    its stored global section — durable knowledge as computed values,
    carrying the proof that they satisfy every local law. -/
structure MemoryState (R : Type*) where
  /-- The memory cells. -/
  V : Type*
  /-- The computation graph over the cells. -/
  F : AlgebraicComputation V R
  /-- The boundary data (consolidated task inputs). -/
  b : V → R
  /-- The stored values: the durable knowledge content. -/
  stored : V → R
  /-- The stored values form a global section of the memory sheaf. -/
  is_section : IsSection F b stored

/-- **Consolidation**: the only admissible change to protected memory —
    a safe extension with matching boundary data.  Either retention
    (`Consolidation.retain`) or growth by new certified cells. -/
structure Consolidation (M M' : MemoryState R) where
  /-- Where each old cell lives in the new memory. -/
  embed : M.V → M'.V
  /-- Old cells keep their wiring and operations. -/
  safe : SheafExtends M.F M'.F embed
  /-- Old cells keep their boundary data. -/
  boundary_eq : ∀ v, M'.b (embed v) = M.b v

/-- **One consolidation step preserves every stored value.**
    Direct reuse of the no-forgetting theorem. -/
theorem Consolidation.preserves {M M' : MemoryState R}
    (c : Consolidation M M') :
    ∀ v, M'.stored (c.embed v) = M.stored v :=
  no_forgetting c.safe c.boundary_eq M.is_section M'.is_section

/-- Retention: keeping memory unchanged is a consolidation. -/
def Consolidation.retain (M : MemoryState R) : Consolidation M M :=
  ⟨id, SheafExtends.refl M.F, fun _ => rfl⟩

/-- Consolidations compose: growing twice is growing once. -/
def Consolidation.comp {M₀ M₁ M₂ : MemoryState R}
    (c₁ : Consolidation M₀ M₁) (c₂ : Consolidation M₁ M₂) :
    Consolidation M₀ M₂ :=
  ⟨c₂.embed ∘ c₁.embed, c₁.safe.comp c₂.safe,
   fun v => (c₂.boundary_eq _).trans (c₁.boundary_eq v)⟩

/-! ### The temporal system -/

/-- A temporal state: unconstrained active state `A_t : α` alongside
    protected memory `M_t`. -/
structure TemporalState (R : Type*) (α : Type*) where
  /-- The plastic, exploratory, self-tuning component (arbitrary). -/
  active : α
  /-- The certified, protected, compositional component. -/
  memory : MemoryState R

variable {α : Type*}

/-- One tick of the system.  The memory component must consolidate safely;
    the active component is UNCONSTRAINED — plasticity is free by
    construction. -/
structure TemporalStep (S S' : TemporalState R α) where
  /-- The memory change is a certified consolidation. -/
  consolidation : Consolidation S.memory S'.memory

/-- Any active jump combined with any consolidation is a valid step:
    plasticity never needs permission. -/
def TemporalStep.plastic {S : TemporalState R α} {M' : MemoryState R}
    (a' : α) (c : Consolidation S.memory M') :
    TemporalStep S ⟨a', M'⟩ :=
  ⟨c⟩

/-- A silent step: the system changes internally (arbitrarily) while
    memory is retained unchanged. -/
def TemporalStep.silent (S : TemporalState R α) (a' : α) :
    TemporalStep S ⟨a', S.memory⟩ :=
  ⟨Consolidation.retain _⟩

/-- The composite memory embedding `i₀ₜ` along a trajectory. -/
def memEmbedUpTo {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1))) (t : ℕ) :
    (traj 0).memory.V → (traj t).memory.V :=
  embedUpTo (fun k => (steps k).consolidation.embed) t

/-- **Lifelong consolidation preserves memory.**

    Along ANY trajectory of the system — arbitrary active dynamics,
    arbitrary consolidations — every stored value of the initial memory is
    intact at every later time:

    `σ_{M_t}(i₀ₜ(v)) = σ_{M₀}(v)`. -/
theorem lifelong_consolidation {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1))) :
    ∀ t v, (traj t).memory.stored (memEmbedUpTo steps t v) =
      (traj 0).memory.stored v :=
  lifelong_no_forgetting (fun k => (steps k).consolidation.safe)
    (fun k => (steps k).consolidation.boundary_eq)
    (fun k => (traj k).memory.is_section)

/-! ### Operator libraries in memory -/

variable [Ring R]

/-- An **operator library** installed in memory `M`: an interpretation of
    the whole expression grammar as memory cells, wired as a safe extension
    of the compiled operator sheaf.  (`opA`, `opM` are the learned
    operations; certification is a separate, checkable property.) -/
structure OpsLibrary (opA opM : R → R → R) {n : ℕ} (ρ : Fin n → R)
    (M : MemoryState R) where
  /-- The memory cell realizing each expression. -/
  interp : Expr R n → M.V
  /-- The grammar's computation graph lives intact inside memory. -/
  safe : SheafExtends (learnedComputation opA opM) M.F interp
  /-- Variable and constant cells carry the intended boundary data. -/
  boundary_eq : ∀ e, M.b (interp e) = exprBoundary ρ e

/-- A certified library: an operator library whose operations carry their
    local certificates. -/
abbrev CertifiedLibrary (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R)
    (M : MemoryState R) :=
  OpsLibrary C.opA C.opM ρ M

/-- The stored memory values, read through the library, form a global
    section of the compiled operator sheaf. -/
theorem OpsLibrary.stored_section {opA opM : R → R → R} {n : ℕ}
    {ρ : Fin n → R} {M : MemoryState R} (L : OpsLibrary opA opM ρ M) :
    IsSection (learnedComputation opA opM) (exprBoundary ρ)
      (M.stored ∘ L.interp) :=
  M.is_section.restrict L.safe L.boundary_eq

/-- **Vocabulary persistence**: a library survives any consolidation —
    the certified vocabulary is monotone along the lifetime. -/
def OpsLibrary.step {opA opM : R → R → R} {n : ℕ} {ρ : Fin n → R}
    {M M' : MemoryState R} (L : OpsLibrary opA opM ρ M)
    (c : Consolidation M M') : OpsLibrary opA opM ρ M' :=
  ⟨c.embed ∘ L.interp, L.safe.comp c.safe,
   fun e => (c.boundary_eq _).trans (L.boundary_eq e)⟩

/-- The library carried along a whole trajectory. -/
def OpsLibrary.upTo {opA opM : R → R → R} {n : ℕ} {ρ : Fin n → R}
    {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    (L₀ : OpsLibrary opA opM ρ (traj 0).memory) :
    (t : ℕ) → OpsLibrary opA opM ρ (traj t).memory
  | 0 => L₀
  | t + 1 => (OpsLibrary.upTo steps L₀ t).step (steps t).consolidation

/-- The carried library reads exactly the transported cells. -/
theorem OpsLibrary.upTo_interp {opA opM : R → R → R} {n : ℕ}
    {ρ : Fin n → R} {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    (L₀ : OpsLibrary opA opM ρ (traj 0).memory) (t : ℕ) (e : Expr R n) :
    (L₀.upTo steps t).interp e = memEmbedUpTo steps t (L₀.interp e) := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (steps t).consolidation.embed ih

/-- Certified library ⟹ exact composition NOW: every expression cell in
    memory stores its denotational value. -/
theorem OpsLibrary.exact {opA opM : R → R → R} {n : ℕ} {ρ : Fin n → R}
    {M : MemoryState R} (L : OpsLibrary opA opM ρ M)
    (hA : ∀ a b, opA a b = a + b) (hM : ∀ a b, opM a b = a * b)
    (e : Expr R n) :
    M.stored (L.interp e) = evalRing ρ e :=
  certified_implies_correct hA hM ρ L.stored_section e

/-! ### The temporal theorems -/

/-- **Temporal exact composition**: once a certified library is
    consolidated, every well-typed expression evaluates exactly at EVERY
    future time, whatever the active state does. -/
theorem temporal_exact_composition {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    {C : CertifiedOps R} {n : ℕ} {ρ : Fin n → R}
    (L₀ : CertifiedLibrary C ρ (traj 0).memory) (t : ℕ) (e : Expr R n) :
    (traj t).memory.stored ((L₀.upTo steps t).interp e) = evalRing ρ e :=
  (L₀.upTo steps t).exact C.certA C.certM e

/-- **The Certified Consolidation Theorem** (capstone).

    For ANY temporal trajectory — arbitrary plastic activity, arbitrary
    certified consolidations — with a certified library installed at time
    zero:

    1. **No forgetting** — every stored value of the initial memory is
       invariant at every time: `σ_{M_t}(i₀ₜ(v)) = σ_{M₀}(v)`; and
    2. **Exact lifelong composition** — every well-typed expression over
       the certified primitives evaluates to its denotational semantics at
       every time: `σ_{M_t}(interp_t(e)) = ⟦e⟧`.

    Plasticity may change `A_t`; only certified safe extension may change
    `M_t`; and under that discipline, capability grows monotonically while
    nothing certified is ever lost. -/
theorem certified_consolidation {traj : ℕ → TemporalState R α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    {C : CertifiedOps R} {n : ℕ} {ρ : Fin n → R}
    (L₀ : CertifiedLibrary C ρ (traj 0).memory) :
    (∀ t v, (traj t).memory.stored (memEmbedUpTo steps t v) =
      (traj 0).memory.stored v) ∧
    (∀ t (e : Expr R n),
      (traj t).memory.stored ((L₀.upTo steps t).interp e) = evalRing ρ e) :=
  ⟨lifelong_consolidation steps, temporal_exact_composition steps L₀⟩

/-! ### Such a system is possible: a concrete witness -/

/-- The expression sheaf itself as a memory state: durable knowledge =
    the exact semantics of every expression. -/
def exprMemory (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R) :
    MemoryState R where
  V := Expr R n
  F := C.computation
  b := exprBoundary ρ
  stored := evalRing ρ
  is_section := evalRing_isSection C.certA C.certM ρ

/-- The identity library on the expression memory. -/
def exprLibrary (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R) :
    CertifiedLibrary C ρ (exprMemory C ρ) where
  interp := id
  safe := SheafExtends.refl _
  boundary_eq := fun _ => rfl

/-- A witness trajectory: the active state follows an ARBITRARY evolution
    `a : ℕ → α` (attention, thresholds, priors, provisional graphs — any
    plasticity whatsoever) while certified memory is retained. -/
def plasticTrajectory (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R)
    (a : ℕ → α) : ℕ → TemporalState R α :=
  fun t => ⟨a t, exprMemory C ρ⟩

/-- Every tick is a valid silent step: internal change, memory retained. -/
def plasticSteps (C : CertifiedOps R) {n : ℕ} (ρ : Fin n → R) (a : ℕ → α) :
    ∀ t, TemporalStep (plasticTrajectory C ρ a t)
      (plasticTrajectory C ρ a (t + 1)) :=
  fun t => TemporalStep.silent (plasticTrajectory C ρ a t) (a (t + 1))

/-- **Such a system is formally possible**: a concrete continually
    "learning" system whose active state evolves arbitrarily, which may
    remain outwardly silent while changing internally, and whose certified
    memory computes the exact semantics of EVERY expression at EVERY
    time. -/
theorem plastic_system_correct (C : CertifiedOps R) {n : ℕ}
    (ρ : Fin n → R) (a : ℕ → α) (t : ℕ) (e : Expr R n) :
    ((plasticTrajectory C ρ a t).memory).stored
      (((exprLibrary C ρ).upTo (plasticSteps C ρ a) t).interp e) =
      evalRing ρ e :=
  temporal_exact_composition (plasticSteps C ρ a) (exprLibrary C ρ) t e

/-! ### The bounded-error branch -/

/-- **Temporal bounded composition**: a library of merely defect-bounded
    (not exactly certified) operations still yields, at EVERY time, a
    global error no worse than the recursive budget:

    `|σ_{M_t}(interp_t(e)) − ⟦e⟧| ≤ B(e)`.

    Certified memory ⟹ exact composition; defect-bounded memory ⟹
    budgeted composition.  Both survive the lifetime. -/
theorem temporal_bounded_composition {α : Type*}
    {traj : ℕ → TemporalState ℝ α}
    (steps : ∀ t, TemporalStep (traj t) (traj (t + 1)))
    {opA opM : ℝ → ℝ → ℝ} {δA δM : ℝ}
    (hA : ∀ a b, |opA a b - (a + b)| ≤ δA)
    (hM : ∀ a b, |opM a b - a * b| ≤ δM)
    {n : ℕ} {ρ : Fin n → ℝ} {P : ℝ} (hρ : ∀ i, |ρ i| ≤ P)
    (L₀ : OpsLibrary opA opM ρ (traj 0).memory) (t : ℕ) (e : Expr ℝ n) :
    |(traj t).memory.stored ((L₀.upTo steps t).interp e) - evalRing ρ e| ≤
      errorBudget δA δM P e :=
  section_defect_bound hA hM hρ (L₀.upTo steps t).stored_section e

end SGC.Sheaf
