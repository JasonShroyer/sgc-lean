/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Renormalization.Lumpability
import SGC.Topology.PadicPathSpace

/-!
# The Cantor Shift Tower: symbolic dynamics as an exact SGC renormalization tower

The missing third leg of the fluid-computation triangle. `DiscreteFluidDynamics`
formalizes the Miranda-program dictionary (currents, h-principle, viscous budget);
`PadicPathSpace` formalizes the Cantor-set substrate (`PathSpace (Fin p) ≃ₜ ℤ_[p]`).
This module formalizes the **Moore leg**: the dynamics that fluid computers actually
embed — the shift map of symbolic dynamics [Moore 1990/1991] — and proves that its
finite cylinder truncations form an **exact (ε = 0) strongly-lumpable tower** of SGC
coarse-grainings whose renormalization maps ARE the shift itself.

## The Dictionary (computation ↔ dynamics ↔ SGC)

| Fluid/symbolic computation (continuum)             | Discrete (this module)                    |
|----------------------------------------------------|-------------------------------------------|
| generalized shift on `A^ℤ` [Moore 1990]            | `pathShift` on `PathSpace (Fin p)`        |
| Cantor transversal of the Reeb/Poincaré section    | `PathSpace (Fin p) ≃ₜ ℤ_[p]` ([PPS] §2)   |
|   ([CMPP] PNAS 2021, §2: points of `C ⊂ D²`)       |   (`pathSpace_homeo_padicInt`)            |
| depth-`n` cylinder observables                     | `Word p n` (`card = p^n`, [PPS] §1)       |
| symbol emission / one machine step                 | `shiftKernel p n` (uniform Bernoulli step)|
| semiconjugacy `π ∘ Φ = σ ∘ π` of the encoding      | `truncate_pathShift` (tower ∘ shift law)  |
| coarse-graining cylinder depth `n+1 → n`           | `tailPartition p n`, strongly lumpable    |
| renormalized machine = same machine                | `shiftTower_quotient_realizes`            |
| unbounded faithful simulation (Turing completeness)| `shiftTower_defect_zero` (ε = 0 exactly)  |

## Why this closes the triangle

[CMPP] embed a Turing machine in a Reeb/Euler flow through Moore's construction:
machine configurations are encoded as points of a Cantor set in a Poincaré section,
and one machine step is the shift. The SGC content proved here: that symbolic layer
is **renormalization-transparent** — truncating history to depth `n` is an EXACT
coarse-graining at every `n` (`shiftTower_stronglyLumpable`), the quotient dynamics
is again the shift one level down (`shiftTower_quotient_realizes`), and the tower
maps intertwine the true Cantor-set shift (`truncate_pathShift`). Lumpability defect
`ε = 0` at every level means the SGC validity horizon `T* = 1/ε` is infinite: **no
coarse-graining barrier obstructs unbounded computation**. Contrast the two finite
budgets already formalized in `DiscreteFluidDynamics`: viscosity cuts computation to
`τ∞ = 1/ν` (`viscous_time_budget`, [PNAS] pp. 8–9), and lumpability defect cuts it
to `1/(νε)` (`damped_validity_budget`). The shift tower is the `ε = 0` pole of that
budget — the sealed-crystal phase where symbolic computation is eternal, which is
exactly why Moore's shifts (and the flows that embed them) can be Turing-complete.

## Continuum anchors (verified sources)

* Moore, PRL 64:2354 & Nonlinearity 4:199 (1990/91): generalized shifts on symbol
  sequences are Turing-universal; embedded in smooth 2D/3D dynamics via Cantor sets.
* Cardona–Miranda–Peralta-Salas–Presas, PNAS 118 (2021): Turing-complete Euler flows —
  machine states on a Cantor set `C` of a disk transversal, dynamics = Moore shift.
* Tao, J. Amer. Math. Soc. (2016) & programme: fluid computation and blow-up.

## Epistemic state

Every declaration below is **kernel-proven** (no `sorry`, no new axioms). The tower
is the finite symbolic layer only; the continuum column of the table is a research
dictionary, not a claim of formalized equivalence. State spaces `Word p n` are the
`truncate`-images of `SGC.Topology.PadicPathSpace`, so the inverse limit of this
tower is literally the space proved homeomorphic to `ℤ_[p]` there ([PPS] §2), i.e.
a Cantor set for every prime `p`.
-/

noncomputable section

namespace SGC.Bridge.CantorShiftTower

open Finset Matrix
open SGC.Topology.PadicPathSpace

/-! ## §1. Words: finite cylinder truncations of the Cantor set -/

/-- Depth-`n` cylinder labels: length-`n` words over the alphabet `Fin p`.
    These are exactly the `truncate`-images of `PathSpace (Fin p)`
    (`SGC.Topology.PadicPathSpace`), with `card = p^n` (`card_truncations`). -/
abbrev Word (p n : ℕ) := Fin n → Fin p

/-- Drop the oldest symbol: the tower projection `Word p (n+1) → Word p n`
    (stated for an arbitrary alphabet so it also applies to `truncate`-images). -/
def tail {A : Type*} {n : ℕ} (u : Fin (n + 1) → A) : Fin n → A := fun i => u i.succ

/-- Shift a fresh symbol `b` into a word: `(w₀…w_{n-1}, b) ↦ (w₁…w_{n-1}, b)`.
    One step of the symbolic machine at truncation depth `n`. -/
def shiftIn {A : Type*} {n : ℕ} (w : Fin n → A) (b : A) : Fin n → A :=
  fun i => if h : (i : ℕ) + 1 < n then w ⟨(i : ℕ) + 1, h⟩ else b

/-- **The tower/shift exchange law**: dropping the oldest symbol commutes with
    shifting in a fresh one. The combinatorial heart of the whole module. -/
lemma tail_shiftIn {A : Type*} {n : ℕ} (u : Fin (n + 1) → A) (b : A) :
    tail (shiftIn u b) = shiftIn (tail u) b := by
  funext i
  simp only [tail, shiftIn, Fin.val_succ]
  by_cases h : (i : ℕ) + 1 < n
  · have h2 : (i : ℕ) + 1 + 1 < n + 1 := by omega
    rw [dif_pos h2, dif_pos h]
    exact congrArg u (Fin.ext (by simp))
  · have h2 : ¬((i : ℕ) + 1 + 1 < n + 1) := by omega
    rw [dif_neg h2, dif_neg h]

/-! ## §2. The shift kernel: one machine step at truncation depth `n` -/

/-- The Bernoulli shift kernel at depth `n`: from word `w`, shift in a uniformly
    random fresh symbol. This is the finite-state shadow of the full shift on
    `PathSpace (Fin p)`; on de Bruijn graphs it is the standard shift walk. -/
def shiftKernel (p n : ℕ) : Matrix (Word p n) (Word p n) ℝ :=
  fun w w' => (∑ b : Fin p, if w' = shiftIn w b then (1 : ℝ) else 0) / p

lemma shiftKernel_nonneg (p n : ℕ) (w w' : Word p n) :
    0 ≤ shiftKernel p n w w' := by
  unfold shiftKernel
  apply div_nonneg _ (Nat.cast_nonneg p)
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> norm_num

/-- The shift kernel is row-stochastic: each word has total outgoing weight 1. -/
theorem shiftKernel_row_sum (p n : ℕ) [NeZero p] (w : Word p n) :
    ∑ w', shiftKernel p n w w' = 1 := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  unfold shiftKernel
  rw [← Finset.sum_div]
  rw [Finset.sum_comm]
  have hinner : ∀ b : Fin p,
      (∑ w' : Word p n, if w' = shiftIn w b then (1 : ℝ) else 0) = 1 := by
    intro b
    rw [Finset.sum_ite_eq' Finset.univ (shiftIn w b) (fun _ => (1 : ℝ))]
    simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-! ## §3. The tail partition and exact lumpability of the tower step -/

/-- The tower partition on depth-`(n+1)` words: identify words with the same tail.
    Coarse state = the last `n` symbols; the forgotten datum is the oldest symbol. -/
def tailPartition (p n : ℕ) : Partition (Word p (n + 1)) where
  rel := ⟨fun u v => tail u = tail v,
    ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
  decRel := fun u v => inferInstanceAs (Decidable (tail u = tail v))

/-- Block membership in the tail partition is tail equality. -/
lemma tailPartition_quot_map_eq_iff {p n : ℕ} (u : Word p (n + 1))
    (B : (tailPartition p n).Quot) :
    (tailPartition p n).quot_map u = B ↔ tail u = tail (Quotient.out B) := by
  constructor
  · intro h
    have hmk : Quotient.mk (tailPartition p n).rel u
        = Quotient.mk (tailPartition p n).rel (Quotient.out B) := by
      rw [Quotient.out_eq]
      exact h
    exact Quotient.eq'.mp hmk
  · intro h
    have hrel : (tailPartition p n).rel.r u (Quotient.out B) := h
    show Quotient.mk (tailPartition p n).rel u = B
    rw [← Quotient.out_eq B]
    exact Quotient.sound hrel

/-- Block row sums of the depth-`(n+1)` shift kernel collapse to the depth-`n`
    shift kernel evaluated at the tail. The computation that makes the tower exact. -/
lemma shiftKernel_row_sum_block (p n : ℕ) (u : Word p (n + 1))
    (B : (tailPartition p n).Quot) :
    row_sum_block (shiftKernel p (n + 1)) (tailPartition p n) u B
      = shiftKernel p n (tail u) (tail (Quotient.out B)) := by
  unfold row_sum_block shiftKernel
  simp_rw [tailPartition_quot_map_eq_iff]
  have step : ∀ u' : Word p (n + 1),
      (if tail u' = tail (Quotient.out B)
        then (∑ b : Fin p, if u' = shiftIn u b then (1 : ℝ) else 0) / p else 0)
      = (∑ b : Fin p,
          if u' = shiftIn u b then (if tail u' = tail (Quotient.out B)
            then (1 : ℝ) else 0) else 0) / p := by
    intro u'
    by_cases hc : tail u' = tail (Quotient.out B)
    · simp [hc]
    · simp [hc]
  simp_rw [step, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hinner : ∀ b : Fin p,
      (∑ u' : Word p (n + 1), if u' = shiftIn u b
        then (if tail u' = tail (Quotient.out B) then (1 : ℝ) else 0) else 0)
      = if tail (shiftIn u b) = tail (Quotient.out B) then (1 : ℝ) else 0 := by
    intro b
    rw [Finset.sum_ite_eq' Finset.univ (shiftIn u b)
        (fun u' => if tail u' = tail (Quotient.out B) then (1 : ℝ) else 0)]
    simp
  simp_rw [hinner, tail_shiftIn]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact if_congr eq_comm rfl rfl

/-- **Exact lumpability of the shift tower**: truncating symbolic history from depth
    `n+1` to depth `n` is a strongly lumpable (defect-free) SGC coarse-graining, for
    every alphabet size and every depth. -/
theorem shiftTower_stronglyLumpable (p n : ℕ) :
    IsStronglyLumpable (shiftKernel p (n + 1)) (tailPartition p n) := by
  intro u v huv B
  show row_sum_block (shiftKernel p (n + 1)) (tailPartition p n) u B
      = row_sum_block (shiftKernel p (n + 1)) (tailPartition p n) v B
  rw [shiftKernel_row_sum_block, shiftKernel_row_sum_block]
  have htail : tail u = tail v := huv
  rw [htail]

/-- **Renormalization = shift (self-similarity of the tower)**: the quotient of the
    depth-`(n+1)` shift kernel by the tail partition IS the depth-`n` shift kernel.
    Coarse-graining the symbolic machine returns the same machine one level down —
    the discrete form of the semiconjugacy that makes Moore/[CMPP] encodings work. -/
theorem shiftTower_quotient_realizes (p n : ℕ) (u u' : Word p (n + 1)) :
    QuotientGeneratorSimple (shiftKernel p (n + 1)) (tailPartition p n)
      ((tailPartition p n).quot_map u) ((tailPartition p n).quot_map u')
      = shiftKernel p n (tail u) (tail u') := by
  rw [quot_gen_eq_row_sum _ _ (shiftTower_stronglyLumpable p n) u,
      shiftKernel_row_sum_block]
  have hout : tail (Quotient.out ((tailPartition p n).quot_map u')) = tail u' :=
    ((tailPartition_quot_map_eq_iff u'
      ((tailPartition p n).quot_map u')).mp rfl).symm
  rw [hout]

/-- **The `ε = 0` pole of the damped validity budget**: the tower step has
    lumpability defect exactly zero. Via `validity_horizon` (`T* = 1/ε`) and
    `damped_validity_budget` (`1/(νε)`, `DiscreteFluidDynamics`), the symbolic
    layer imposes NO finite horizon on computation — only dissipation `ν` does. -/
theorem shiftTower_defect_zero (p n : ℕ) :
    IsRowSumApproxLumpable (shiftKernel p (n + 1)) (tailPartition p n) 0 :=
  strong_implies_approx_zero _ _ (shiftTower_stronglyLumpable p n)

/-! ## §4. The generator form -/

/-- The shift generator `L = K − I`: continuous-time form of the machine step,
    the object the SGC trajectory/horizon theorems speak about. -/
def shiftGenerator (p n : ℕ) : Matrix (Word p n) (Word p n) ℝ :=
  shiftKernel p n - 1

/-- The shift generator is conservative (row sums vanish). -/
theorem shiftGenerator_row_sum_zero (p n : ℕ) [NeZero p] (w : Word p n) :
    ∑ w', shiftGenerator p n w w' = 0 := by
  unfold shiftGenerator
  simp only [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, shiftKernel_row_sum p n w]
  have hone : (∑ w' : Word p n, (1 : Matrix (Word p n) (Word p n) ℝ) w w') = 1 := by
    simp [Matrix.one_apply]
  rw [hone, sub_self]

/-- Block row sums are additive under matrix subtraction. -/
lemma row_sum_block_sub {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℝ) (P : Partition V) (i : V) (Bq : P.Quot) :
    row_sum_block (A - B) P i Bq = row_sum_block A P i Bq - row_sum_block B P i Bq := by
  unfold row_sum_block
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : P.quot_map k = Bq <;> simp [h]

/-- Block row sums of the identity matrix are the block indicator. -/
lemma row_sum_block_one {V : Type*} [Fintype V] [DecidableEq V]
    (P : Partition V) (i : V) (Bq : P.Quot) :
    row_sum_block (1 : Matrix V V ℝ) P i Bq = if P.quot_map i = Bq then 1 else 0 := by
  unfold row_sum_block
  have hterm : ∀ k : V, (if P.quot_map k = Bq then (1 : Matrix V V ℝ) i k else 0)
      = if k = i then (if P.quot_map k = Bq then 1 else 0) else 0 := by
    intro k
    rw [Matrix.one_apply]
    by_cases hk : k = i
    · subst hk; simp [eq_comm]
    · have : ¬(i = k) := fun h => hk h.symm
      simp [hk, this]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' Finset.univ i (fun k => if P.quot_map k = Bq then (1 : ℝ) else 0)]
  simp

/-- **Exact lumpability, generator form**: the conservative generator of the tower
    step is strongly lumpable as well — subtracting the identity never breaks
    block structure. -/
theorem shiftGenerator_stronglyLumpable (p n : ℕ) :
    IsStronglyLumpable (shiftGenerator p n.succ) (tailPartition p n) := by
  intro u v huv B
  show row_sum_block (shiftGenerator p (n + 1)) (tailPartition p n) u B
      = row_sum_block (shiftGenerator p (n + 1)) (tailPartition p n) v B
  unfold shiftGenerator
  rw [row_sum_block_sub, row_sum_block_sub, row_sum_block_one, row_sum_block_one]
  have hK := shiftTower_stronglyLumpable p n u v huv B
  have hKr : row_sum_block (shiftKernel p (n + 1)) (tailPartition p n) u B
      = row_sum_block (shiftKernel p (n + 1)) (tailPartition p n) v B := hK
  rw [hKr]
  have hquot : (tailPartition p n).quot_map u = (tailPartition p n).quot_map v :=
    Quotient.sound huv
  rw [hquot]

/-! ## §4b. Eternal validity: exact closure at every discrete horizon -/

/-- **Eternal validity of the symbolic coarse-graining**: for EVERY number of machine
    steps `m`, evolving fine and then coarse-graining equals coarse-graining and then
    evolving the quotient machine — `K^m · lift = lift · (K̄)^m` with no error term.
    This is the `ε = 0` / `T* = ∞` pole of the validity-horizon story
    (`validity_horizon`, `damped_validity_budget`): the finite budgets of the fluid
    computer come from viscosity alone, never from the symbolic tower. -/
theorem shiftTower_eternal_closure (p n : ℕ) (m : ℕ) :
    (shiftKernel p (n + 1)) ^ m * lift_matrix (tailPartition p n)
      = lift_matrix (tailPartition p n)
        * (QuotientGeneratorSimple (shiftKernel p (n + 1)) (tailPartition p n)) ^ m :=
  intertwining_pow _ _ (shiftTower_stronglyLumpable p n) m

/-! ## §5. The Cantor glue: tower projections intertwine the true shift -/

/-- The one-sided shift on path space — Moore's machine step on the full
    (infinite-precision) symbolic state. Under `pathSpaceEquivPadicInt` this is
    the digit shift `y ↦ (y − a₀(y))/p` on the p-adic Cantor set `ℤ_[p]`. -/
def pathShift (A : Type*) : PathSpace A → PathSpace A := fun x k => x (k + 1)

/-- **Semiconjugacy of truncation**: truncating the shifted path equals the tower
    projection of the deeper truncation. Together with `pathSpace_homeo_padicInt`
    (`PadicPathSpace` §2) this exhibits the finite tower of §3 as the cylinder
    shadow of the genuine Cantor-set shift — the discrete counterpart of reading
    a [CMPP] fluid computer through Poincaré sections of increasing resolution. -/
theorem truncate_pathShift (A : Type*) (n : ℕ) (x : PathSpace A) :
    truncate A n (pathShift A x) = tail (truncate A (n + 1) x) := rfl

end SGC.Bridge.CantorShiftTower
