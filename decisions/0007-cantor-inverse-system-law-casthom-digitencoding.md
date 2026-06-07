---
method: "Lake-gated proof of the Cantor-layer inverse-system law: digitEncoding intertwines depth restriction (drop top digit) with ZMod.castHom (reduce mod p^n)"
status: VALIDATED
domain: topology
replaces: []
replaced_by: []
core_rollout:
  retrieved: ["0002-proof-strategy-fintype-firewall", "0003-check-statement-strength-before-discharging", "0005-math-trivial-is-not-lean-cheap"]
  reused_with_reward: ["0005-math-trivial-is-not-lean-cheap"]   # r=1, first measured reuse on a DIFFERENT proof
evidence:
  - "C:/Lean4 Projects @ cantor-layer-wip commit 95bf170"
  - src/SGC/Topology/PadicPathSpace.lean
  - C:/Users/Jason/sgc-second-brain/logs/build_cantor_intertwine.txt
  - C:/Users/Jason/sgc-second-brain/logs/axioms_cantor_intertwine.txt
date: 2026-06-07
---
# Cantor-layer inverse-system law: `castHom_digitEncoding`

## Verdict

`castHom_digitEncoding` is **machine-verified** (`lake build` exit 0; the only `sorry`
warning is the pre-existing homeomorphism keystone at L80). Axiom audit:
`[propext, Classical.choice, Quot.sound]` — **no new SGC axioms** (directive held; tree
stays at 229). **First-try success**, on a CORE rollout that retrieved insights 0002/0003/0005
*before* writing a line.

The theorem is the finite-level content of "symbolic depth-`n` truncation = `PadicInt.toZModPow n`":
for `f : Fin (n+1) → Fin p`,
`ZMod.castHom (pow_dvd_pow p n.le_succ) (ZMod (p^n)) (digitEncoding p (n+1) f) = digitEncoding p n (fun i => f i.castSucc)`.
It is the `n → n+1` **commuting square** that makes the `digitEncoding`s an iso of inverse
systems — the "real content" the spec (§4.2) flagged behind the content-light bare
homeomorphism.

## When to use / When NOT to use

- USE this route for "encode ∘ restrict = reduce ∘ encode" over a base-`p` Horner map:
  1. unfold to the Nat Horner value (`simp only [digitEncoding, finEquivZMod, Equiv.trans_apply, Equiv.coe_fn_mk]`);
  2. push the ring hom through the cast with `map_natCast` (castHom is a `RingHom`);
  3. `finFunctionFinEquiv_apply` to expose `∑ i, (f i) * m^i` (it is `rfl`);
  4. peel the top digit with `Fin.sum_univ_castSucc` + `Fin.val_last`;
  5. zero it with `Nat.cast_mul` then `ZMod.natCast_self` (`↑(p^n) = 0`), `mul_zero`, `add_zero`;
  6. align the surviving sum with `Fin.coe_castSucc`.
- **Do NOT `push_cast` the top-digit term.** `push_cast` rewrites `↑(p^n)` to `(↑p)^n`,
  which is **not** syntactically `0`, so `ZMod.natCast_self` stops firing and the term
  survives. Keep the cast on the *composite* `p^n` and use TARGETED `Nat.cast_mul` +
  `ZMod.natCast_self`. (This is a sharpening of insight 0005: targeted cast lemmas over
  blanket `push_cast`, same spirit as "targeted `rw [Finset.mul_sum]`, never blanket `simp`".)

## Why (SGC)

The keystone chain (spec §4): the bare `PathSpace ≃ₜ ℤ_[p]` is content-light (all Cantor
spaces are homeomorphic); the substance is the **iso of inverse systems commuting with the
quotient maps `Πₙ`**. `castHom_digitEncoding` is exactly one rung of that commuting tower,
proven at the finite, `[Fintype]`-internal level (insight 0002 — firewall-internal targets
first). It reduces the remaining `pathSpace_homeo_padicInt` debt to *assembling* these finite
squares into the projective-limit homeomorphism against `PadicInt.toZModPow` — no longer an
open question of "is there content", but a construction task.

Insight-0003 guard cleared: the statement is a genuine equality in `ZMod (p^n)` (contentful
for `p ≥ 2`), not an `∧ True` / free-existential discharge.

## Evidence

- Theorem PROVEN — `src/SGC/Topology/PadicPathSpace.lean` (`castHom_digitEncoding`),
  research repo `cantor-layer-wip` commit `95bf170`.
- Build PASSES — `logs/build_cantor_intertwine.txt` (39s cold, exit 0),
  `logs/build_cantor_final.txt` (post-revert, exit 0). Only L80 homeo `sorry` remains.
- Axiom audit — `logs/axioms_cantor_intertwine.txt`:
  `castHom_digitEncoding depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Canonical implementation

Six-line tactic proof (see source). The crux is step 5/6: the top digit `f (Fin.last n)`
carries weight `p^n`, which is `0` in `ZMod (p^n)` — so the depth-`n+1` encoding reduces
exactly to the depth-`n` encoding of the restricted path. That is the arithmetic shadow of
"the (n+1)-th symbol is invisible to the depth-`n` observer".
