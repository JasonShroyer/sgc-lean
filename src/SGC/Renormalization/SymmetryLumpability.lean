/-
Copyright (c) 2026 Jason Shroyer. All rights reserved.
Released under Apache 2.0 license.
-/
import SGC.Renormalization.Lumpability
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Symmetry Implies Exact Lumpability — and Is Strictly Weaker Than It

The discrete, finite-state form of the symmetry-first definition of
macroscopic law (the effective-field-theory program for hydrodynamics:
Dubovsky-Hui-Nicolis-Son arXiv:1210.1561, perfect fluids from the
parcel-swapping symmetry; Crossley-Glorioso-Liu arXiv:1511.03646, the
dissipative EFT — see the Quanta overview of 2026-08-17):

> **If a group acts on the microscopic state space and the generator is
> equivariant, the orbit partition is strongly lumpable** — the macroscopic
> (quotient) dynamics is exactly closed, for every initial distribution.

Swapping microstates within an orbit is "free" (the generator cannot tell),
and the macro-law is a consequence — symmetry over substance, at the
finite-state layer, as a kernel theorem (`orbitPartition_stronglyLumpable`).

## Established vocabulary

| This library | Established term |
|---|---|
| `IsStronglyLumpable` (equal block row sums) | strong lumpability (Dynkin criterion); **equitable partition** of the weighted digraph |
| orbit partition of an equivariant generator | symmetry reduction / orbit quotient |
| `IsRowSumApproxLumpable` | approximate lumpability (cf. local-symmetry routes in the agent-based-models literature) |

`IsEquitable` is provided as the searchable alias for the established name.

## The converse fails — and that is the finding

`counterexample_lumpable_not_symmetric`: an explicit four-state generator
whose two-block partition is strongly lumpable while its **only**
generator-equivariant permutation is the identity. Hence every orbit
partition of every automorphism group of this generator is the discrete
partition — the lumpable two-block structure is realized by NO symmetry.

> Symmetry is a sufficient mechanism for exact consolidation, but exact
> consolidation is strictly more general than symmetry quotienting.

This is where SGC's theory of emergence exceeds the symmetry-first program:
macroscopic law without a group. (The star example
`CurvatureQuotient.StarExample` is the complementary instance — an orbit
partition, i.e. THIS module's theorem done by hand for `K_{1,6}`.)

## Honest scope

* Finite state spaces, finite (or finitely-acting) groups. No claim about
  the continuum EFT; the connection is a shared symmetry principle, not an
  identification (see the vetted-intel audit, vault 2026-08-18).
* The dictionary "dynamical KMS ↔ local detailed balance" lives in the
  thermodynamic register (`EntropyProduction`, `DissipationFloor`), not
  here; this module is the spatial-symmetry half only.
-/

namespace SGC.Renormalization.SymmetryLumpability

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1. Equivariance and the orbit partition -/

/-- A generator is **equivariant** under a group action when the action
cannot be detected by the rates: `L (g•x) (g•y) = L x y`. The finite-state
form of the parcel-swapping symmetry. -/
def GeneratorEquivariant (G : Type*) [Group G] [MulAction G V]
    (L : Matrix V V ℝ) : Prop :=
  ∀ (g : G) (x y : V), L (g • x) (g • y) = L x y

/-- **Vocabulary alias**: strong lumpability is the equitable-partition
condition (Dynkin criterion) for the weighted digraph of the generator. -/
abbrev IsEquitable (L : Matrix V V ℝ) (P : SGC.Partition V) : Prop :=
  SGC.IsStronglyLumpable L P

/-- The **orbit partition** of a group action, packaged for the lumpability
machinery. Blocks are the `G`-orbits. -/
def orbitPartition (G : Type*) [Group G] [Fintype G] [MulAction G V] :
    SGC.Partition V where
  rel := MulAction.orbitRel G V
  decRel := fun x y =>
    decidable_of_iff (∃ g : G, g • y = x) (by
      show (∃ g : G, g • y = x) ↔ (MulAction.orbitRel G V).r x y
      exact Iff.rfl)

variable {G : Type*} [Group G] [Fintype G] [MulAction G V]

omit [Fintype V] in
/-- Acting by `g` does not change the orbit-partition block. -/
lemma orbitPartition_quot_map_smul (g : G) (w : V) :
    (orbitPartition G).quot_map ((g : G) • w) = (orbitPartition G).quot_map w := by
  apply Quotient.sound
  exact ⟨g, rfl⟩

/-! ## §2. The theorem: symmetry ⟹ exact lumpability -/

/-- **Symmetry implies exact lumpability.** If the generator is equivariant
under a group action, its orbit partition is strongly lumpable: the
macroscopic dynamics on orbits is exactly closed. The proof is the finite
reindexing `z ↦ g • z` of the block row sum — swapping within an orbit is
free, so all states of an orbit present identical aggregate rates to every
block. The finite-state shadow of "a fluid is defined by its swapping
symmetry, and the macroscopic law follows". -/
theorem orbitPartition_stronglyLumpable (L : Matrix V V ℝ)
    (hL : GeneratorEquivariant G L) :
    SGC.IsStronglyLumpable L (orbitPartition G) := by
  intro x y hxy b_bar
  obtain ⟨g, hg⟩ : ∃ g : G, g • y = x := hxy
  subst hg
  -- reindex the left sum by the permutation z ↦ g • z
  have hre : (∑ z : V, if (orbitPartition G).quot_map z = b_bar
        then L ((g : G) • y) z else 0)
      = ∑ w : V, if (orbitPartition G).quot_map ((g : G) • w) = b_bar
        then L ((g : G) • y) ((g : G) • w) else 0 :=
    (Equiv.sum_comp (MulAction.toPerm g)
      (fun z => if (orbitPartition G).quot_map z = b_bar
        then L ((g : G) • y) z else 0)).symm
  rw [hre]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [orbitPartition_quot_map_smul g w, hL g y w]

/-- The orbit partition has zero approximate-lumpability defect: the ε = 0
pole, by symmetry. -/
theorem orbitPartition_approx_zero (L : Matrix V V ℝ)
    (hL : GeneratorEquivariant G L) :
    SGC.IsRowSumApproxLumpable L (orbitPartition G) 0 :=
  SGC.strong_implies_approx_zero L _ (orbitPartition_stronglyLumpable L hL)

/-- The orbit partition is equitable (vocabulary form). -/
theorem orbitPartition_isEquitable (L : Matrix V V ℝ)
    (hL : GeneratorEquivariant G L) :
    IsEquitable L (orbitPartition G) :=
  orbitPartition_stronglyLumpable L hL

/-! ## §3. The converse fails: lumpable without symmetry

The four-state generator below (states `0,1 | 2,3`, blocks `A | B`):

```
        A = {0, 1}                B = {2, 3}
  0 ──1──────────────▶ 2    2 ──1──────────────▶ 0
  1 ──2/5────────────▶ 2    3 ──1──────────────▶ 1
  1 ──3/5────────────▶ 3
```

Every `A`-state sends total rate `1` to `B` and every `B`-state sends total
rate `1` to `A`, so the two-block partition is strongly lumpable. But state
`0` concentrates its outflow on one target while state `1` splits `2/5, 3/5`
— the rate multisets differ, so no non-identity permutation preserves `L`.
Every automorphism-orbit partition of this generator is therefore discrete,
and the lumpable two-block structure is realized by no symmetry. -/

/-- The asymmetric four-state generator. Rows sum to zero; off-diagonal
rates nonnegative. Written with decidable guards so that `fin_cases` +
`norm_num` evaluate every entry reliably. -/
noncomputable def Lex : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  if i = j then -1
  else if (i : ℕ) = 0 ∧ (j : ℕ) = 2 then 1
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 then 2/5
  else if (i : ℕ) = 1 ∧ (j : ℕ) = 3 then 3/5
  else if (i : ℕ) = 2 ∧ (j : ℕ) = 0 then 1
  else if (i : ℕ) = 3 ∧ (j : ℕ) = 1 then 1
  else 0

/-- The two-block partition `{0,1} | {2,3}`. -/
def Pex : SGC.Partition (Fin 4) where
  rel := ⟨fun x y => ((x : ℕ) ≤ 1 ↔ (y : ℕ) ≤ 1),
    ⟨fun _ => Iff.rfl, Iff.symm, Iff.trans⟩⟩
  decRel := fun x y => inferInstanceAs (Decidable (((x : ℕ) ≤ 1) ↔ ((y : ℕ) ≤ 1)))

lemma Pex_mk_eq_mk {z w : Fin 4} :
    (Quotient.mk Pex.rel z = Quotient.mk Pex.rel w) ↔ (((z : ℕ) ≤ 1) ↔ ((w : ℕ) ≤ 1)) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The two-block partition is strongly lumpable (equitable) for `Lex`. -/
theorem Lex_stronglyLumpable : SGC.IsStronglyLumpable Lex Pex := by
  intro x y hxy b_bar
  induction b_bar using Quotient.ind with
  | _ w =>
    have hxy' : (((x : ℕ) ≤ 1) ↔ ((y : ℕ) ≤ 1)) := hxy
    show (∑ z : Fin 4, if Pex.quot_map z = Quotient.mk Pex.rel w then Lex x z else 0)
      = ∑ z : Fin 4, if Pex.quot_map z = Quotient.mk Pex.rel w then Lex y z else 0
    simp only [SGC.Partition.quot_map, Pex_mk_eq_mk]
    fin_cases x <;> fin_cases y <;> fin_cases w <;>
      simp_all [Fin.sum_univ_four, Lex] <;> norm_num

/-- The only value `3/5` in `Lex` sits at `(1, 3)`. -/
lemma Lex_eq_three_fifths {a b : Fin 4} (h : Lex a b = 3/5) : a = 1 ∧ b = 3 := by
  fin_cases a <;> fin_cases b <;>
    first
      | exact ⟨rfl, rfl⟩
      | (exfalso; revert h; norm_num [Lex])

/-- The only value `2/5` in `Lex` sits at `(1, 2)`. -/
lemma Lex_eq_two_fifths {a b : Fin 4} (h : Lex a b = 2/5) : a = 1 ∧ b = 2 := by
  fin_cases a <;> fin_cases b <;>
    first
      | exact ⟨rfl, rfl⟩
      | (exfalso; revert h; norm_num [Lex])

/-- **The generator has no symmetry**: the only permutation of states that
preserves `Lex` is the identity. -/
theorem Lex_automorphism_trivial (σ : Equiv.Perm (Fin 4))
    (hσ : ∀ x y, Lex (σ x) (σ y) = Lex x y) : σ = 1 := by
  -- the unique rate 3/5 pins σ 1 = 1 and σ 3 = 3
  have h13 : Lex (σ 1) (σ 3) = 3/5 := by rw [hσ 1 3]; norm_num [Lex, Fin.ext_iff]
  obtain ⟨hσ1, hσ3⟩ := Lex_eq_three_fifths h13
  -- the unique rate 2/5 pins σ 2 = 2
  have h12 : Lex (σ 1) (σ 2) = 2/5 := by rw [hσ 1 2]; norm_num [Lex, Fin.ext_iff]
  obtain ⟨-, hσ2⟩ := Lex_eq_two_fifths h12
  -- injectivity forces σ 0 = 0
  have hσ0 : σ 0 = 0 := by
    have h01 : σ 0 ≠ 1 := fun h => absurd (σ.injective (h.trans hσ1.symm)) (by decide)
    have h02 : σ 0 ≠ 2 := fun h => absurd (σ.injective (h.trans hσ2.symm)) (by decide)
    have h03 : σ 0 ≠ 3 := fun h => absurd (σ.injective (h.trans hσ3.symm)) (by decide)
    have hall : ∀ v : Fin 4, v ≠ 1 → v ≠ 2 → v ≠ 3 → v = 0 := by decide
    exact hall _ h01 h02 h03
  ext z
  fin_cases z <;> simp [hσ0, hσ1, hσ2, hσ3]

/-- **The converse of `orbitPartition_stronglyLumpable` fails.** `Lex` is
exactly lumpable over the nontrivial two-block partition, yet admits no
nontrivial symmetry: exact consolidation is strictly more general than
symmetry quotienting. Symmetry is a sufficient mechanism for emergence of a
closed macro-law — not its definition. -/
theorem counterexample_lumpable_not_symmetric :
    SGC.IsStronglyLumpable Lex Pex ∧
    (∀ σ : Equiv.Perm (Fin 4), (∀ x y, Lex (σ x) (σ y) = Lex x y) → σ = 1) ∧
    Pex.quot_map 0 = Pex.quot_map 1 ∧ Pex.quot_map 0 ≠ Pex.quot_map 2 :=
  ⟨Lex_stronglyLumpable, Lex_automorphism_trivial,
    Quotient.sound (show (((0 : Fin 4) : ℕ) ≤ 1 ↔ ((1 : Fin 4) : ℕ) ≤ 1) by decide),
    fun h => by
      have h' : (((0 : Fin 4) : ℕ) ≤ 1 ↔ ((2 : Fin 4) : ℕ) ≤ 1) := Quotient.exact h
      exact absurd h' (by decide)⟩

end SGC.Renormalization.SymmetryLumpability
