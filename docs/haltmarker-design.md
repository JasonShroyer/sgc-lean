# haltMarker compiler — design note (2026-08-09)

Goal: upgrade `SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff` from a
marker-parameterized gadget lemma into a genuine statement about Turing
machines, by supplying the computable compiler `(M, w) ↦ haltMarker M w` and
composing. Target module: `SGC.Bridge.HaltingCompiler`.

## Machine model (fixed)

Mathlib's Post-Turing machine layer `Turing.TM0`
(`Mathlib.Computability.PostTuringMachine`):

- `Machine Γ Λ := Λ → Γ → Option (Λ × Stmt Γ)` with `[Inhabited Λ]`
  (default = starting state), `[Inhabited Γ]` (default = blank).
- `step M : Cfg Γ Λ → Option (Cfg Γ Λ)`; `none` = halt.
- `init w : Cfg Γ Λ` places input `w : List Γ` on the tape.
- Canonical halting predicate: `(TM0.eval M w).Dom`, where
  `TM0.eval M w = (Turing.eval (step M) (init w)).map (·.Tape.right₀)` and
  `Turing.eval` is the `PFun.fix` of the step relation. This is Mathlib's own
  notion — we do NOT invent a private halting predicate.

## The compiler (total, structurally recursive — no choice in the definition)

For any `f : σ → Option σ` define the fuel-indexed simulation

```
multistep f a : ℕ → Option σ
  | 0     => some a
  | n + 1 => (multistep f a n).bind f
```

and the exact-step halting marker (`Bool`-valued, total):

```
haltMarkerNat M w n := (multistep (step M) (init w) n).isSome
                        && !(multistep (step M) (init w) (n+1)).isSome
haltMarker M w : ℤ → Bool := fun i => if 0 ≤ i then haltMarkerNat M w i.toNat else false
```

`haltMarker M w i = true` iff the machine performs its `none` transition at
exactly fuel `i` (`i ≥ 0`). No `DecidableEq` on configurations is needed:
only `Option.isSome` is inspected.

## Obligations (the reviewer's list, items 1–5)

1. Machine/input representation: `(M : Machine Γ Λ, w : List Γ)`. ✓ fixed above.
2. Exact-step predicate: `haltMarkerNat` (Bool, total). ✓
3. Total computable Boolean realization: structural recursion over ℕ;
   the ℤ-extension is an `if 0 ≤ i` guard (decidable). ✓
4. Correctness + at-most-once:
   - `multistep_eq_none_mono` : `none` is absorbing ⇒
     `haltMarker_at_most_once` : marker fires at most once (hypothesis `hone`
     of `cd0_haltW_iff` discharged).
   - `haltMarker_false_iff_isSome` : all-false ⇔ every fuel level is live.
5. Bridge to Mathlib's halting predicate:
   - `reaches_iff_multistep` : `Reaches f a b ↔ ∃ n, multistep f a n = some b`
     (induction over `Relation.ReflTransGen` / over fuel).
   - `evalDom_iff_multistep` : `(Turing.eval f a).Dom ↔ ∃ n, multistep f a n = none`
     (via `Turing.mem_eval`, `Part.dom_iff_mem`).

## Target theorems

```
theorem cd0_compiled_iff (M : Machine Γ Λ) (w : List Γ) :
    CD0 (haltW (haltMarker M w)) ↔ ¬ (TM0.eval M w).Dom

theorem not_cd0_compiled_iff (M : Machine Γ Λ) (w : List Γ) :
    ¬ CD0 (haltW (haltMarker M w)) ↔ (TM0.eval M w).Dom
```

Reading: deciding the global Bakry-Émery bound `CD(0,∞)` for the compiled
generator family `{haltW (haltMarker M w)}` is exactly deciding non-halting
of `(M, w)` — the complement of the halting problem, over Mathlib's own TM
model. Together with the standard fact that halting for `TM0` is undecidable
(classical, not re-proved here) this is the honest Π⁰₁-hardness statement.

## Epistemic scope (what is NOT claimed)

- Π⁰₁ *membership* (upper semicomputability of `inf κ`) is a prose remark,
  not formalized here.
- No claim that `TM0` halting undecidability itself is formalized in this
  module; the reduction is the contribution.
- Audit standard: both target theorems must close over exactly
  `[propext, Classical.choice, Quot.sound]`; on success they join
  `scripts/AxiomAudit.lean`.
