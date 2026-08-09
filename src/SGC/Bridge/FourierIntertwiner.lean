/-
# The Finite Fourier Intertwiner: coarse-graining annihilates the top frequency band

This file is the **torus / frequency-side mirror** of `SGC/Bridge/TruncationProjector.lean`.

Sealed companion results (ε = 0):
* `TruncationProjector.coarseProjector_eq_truncation_average` — the renormalization
  coarse-graining projector = the local average over the last `p`-adic digit;
* `TruncationTower.digitEncoding_truncationQuotient` — that coarse-graining quotient
  map *is* the `p`-adic residue map `ZMod.castHom : ZMod (p^(n+1)) → ZMod (p^n)`.

Here we cross to the **frequency / torus** side of the §2 filtration dictionary and
prove, on the finite Fourier transform `ZMod.dft` (notation `𝓕`), the exact statement

> a function that is constant on the fibers of `castHom` (a *coarse* function, i.e. one
> pulled back from `ZMod (p^n)`) has a **vanishing** Fourier coefficient at every
> frequency `k` outside the `p`-divisible band (`↑(p^n) * k ≠ 0`).

In the band-limited picture `Vₙ = span {e^{2πi k x}}` this is precisely
"coarse-graining = reduce mod `p^n` = kill the top frequency band".  It converts the
prose §2 entry of the p-adic ↔ torus bridge sketch into a kernel-checked fact, with no
new axioms.

The proof is the honest one-line idea made finite: a `c`-periodic function `Φ` satisfies
`𝓕 Φ k = χ(-c·k) • 𝓕 Φ k` (reindex the DFT sum by `+ c` and use multiplicativity of the
standard additive character `χ = stdAddChar`); when `χ(-c·k)` is nontrivial the scalar
`1 - χ(-c·k)` is a unit, forcing `𝓕 Φ k = 0`.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Equiv.Basic

open Finset AddChar ZMod

namespace SGC.Bridge

/-- **Periodic functions are band-limited.**
If `Φ : ZMod N → E` is invariant under translation by `c` (`Φ (y + c) = Φ y`) then its
discrete Fourier coefficient `𝓕 Φ k` vanishes at every frequency `k` for which the
standard additive character is nontrivial on `c · k` (`stdAddChar (-(c * k)) ≠ 1`).

This is the abstract "coarse-graining kills the top band" lemma; the `c = p^n`
specialisation is `dft_pullback_eq_zero_of_band`. -/
theorem dft_eq_zero_of_period {N : ℕ} [NeZero N] {E : Type*}
    [AddCommGroup E] [Module ℂ E]
    (Φ : ZMod N → E) (c k : ZMod N)
    (hperiod : ∀ y, Φ (y + c) = Φ y)
    (hk : stdAddChar (-(c * k)) ≠ 1) :
    𝓕 Φ k = 0 := by
  have key : 𝓕 Φ k = stdAddChar (-(c * k)) • 𝓕 Φ k := by
    rw [dft_apply, Finset.smul_sum,
        ← Equiv.sum_comp (Equiv.addRight c) fun j => stdAddChar (-(j * k)) • Φ j]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addRight]
    rw [hperiod j, add_mul, neg_add, map_add_eq_mul,
        mul_comm (stdAddChar (-(j * k))) (stdAddChar (-(c * k))), mul_smul]
  have hne : (1 : ℂ) - stdAddChar (-(c * k)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  have hz : (1 - stdAddChar (-(c * k))) • 𝓕 Φ k = 0 := by
    rw [sub_smul, one_smul, ← key, sub_self]
  calc 𝓕 Φ k
      = (1 - stdAddChar (-(c * k)))⁻¹ • ((1 - stdAddChar (-(c * k))) • 𝓕 Φ k) :=
        (inv_smul_smul₀ hne (𝓕 Φ k)).symm
    _ = (1 - stdAddChar (-(c * k)))⁻¹ • (0 : E) := by rw [hz]
    _ = 0 := smul_zero _

/-- **Converse: a band-supported spectrum forces periodicity.**
If the discrete Fourier transform of `Φ` vanishes at every frequency where the standard
additive character is nontrivial on `c · k`, then `Φ` is invariant under translation by `c`.

Proved by Fourier inversion (`dft_dft`): the inversion sum `(N:ℂ) • Φ y = ∑ₖ χ(k·y)·𝓕Φ k`
only sees on-band frequencies, and on the band the `+c` translation contributes the trivial
factor `χ(k·c) = 1`; off the band `𝓕Φ k = 0`. -/
theorem periodic_of_dft_eq_zero_off_band {N : ℕ} [NeZero N] {E : Type*}
    [AddCommGroup E] [Module ℂ E]
    (Φ : ZMod N → E) (c : ZMod N)
    (hband : ∀ k, stdAddChar (-(c * k)) ≠ 1 → 𝓕 Φ k = 0) :
    ∀ y, Φ (y + c) = Φ y := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hinv : ∀ z, ∑ k, stdAddChar (k * z) • 𝓕 Φ k = (N : ℂ) • Φ z := by
    intro z
    have h2 := congrFun (dft_dft Φ) (-z)
    rw [dft_apply] at h2
    simp only [mul_neg, neg_neg] at h2
    exact h2
  have hcancel : ∀ k, stdAddChar (k * c) • 𝓕 Φ k = 𝓕 Φ k := by
    intro k
    by_cases h : stdAddChar (-(c * k)) = 1
    · have hck : stdAddChar (c * k) = 1 := by
        rw [map_neg_eq_inv, inv_eq_one] at h; exact h
      rw [mul_comm k c, hck, one_smul]
    · rw [hband k h, smul_zero]
  intro y
  have key : (N : ℂ) • Φ (y + c) = (N : ℂ) • Φ y := by
    rw [← hinv (y + c), ← hinv y]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_add, map_add_eq_mul, mul_smul, hcancel k]
  calc Φ (y + c) = (N : ℂ)⁻¹ • ((N : ℂ) • Φ (y + c)) := (inv_smul_smul₀ hN _).symm
    _ = (N : ℂ)⁻¹ • ((N : ℂ) • Φ y) := by rw [key]
    _ = Φ y := inv_smul_smul₀ hN _

/-- **Exact spectral characterization of periodicity (Littlewood–Paley building block).**
`Φ` is invariant under translation by `c` **iff** its discrete Fourier spectrum is supported
on the band `{k | stdAddChar (-(c*k)) = 1}` — the frequencies annihilated by `c`.

So the `c`-periodic functions and the `c`-band-limited functions are the *same* subspace.
Iterating over the `castHom` tower turns this into the orthogonal band decomposition that
underlies the p-adic frequency ladder (each new scale = one new band). -/
theorem periodic_iff_dft_eq_zero_off_band {N : ℕ} [NeZero N] {E : Type*}
    [AddCommGroup E] [Module ℂ E]
    (Φ : ZMod N → E) (c : ZMod N) :
    (∀ y, Φ (y + c) = Φ y) ↔ (∀ k, stdAddChar (-(c * k)) ≠ 1 → 𝓕 Φ k = 0) :=
  ⟨fun hper k hk => dft_eq_zero_of_period Φ c k hper hk,
   periodic_of_dft_eq_zero_off_band Φ c⟩

/-- **The finite Fourier intertwiner (torus side of the §2 dictionary).**
A *coarse* function — one pulled back along the `p`-adic residue map
`castHom : ZMod (p^(n+1)) → ZMod (p^n)` from a function `g` on the coarser ring — has a
vanishing discrete Fourier coefficient at every frequency `k` off the `p`-divisible band,
i.e. whenever `↑(p^n) * k ≠ 0` in `ZMod (p^(n+1))`.

Equivalently: passing to the coarse grain (`reduce mod p^n`) annihilates the top
frequency band.  This mirrors `TruncationTower.digitEncoding_truncationQuotient` (which
identifies that coarse-graining quotient with `castHom`) on the Fourier / torus side. -/
theorem dft_pullback_eq_zero_of_band {p n : ℕ} [Fact p.Prime]
    (g : ZMod (p ^ n) → ℂ) (k : ZMod (p ^ (n + 1)))
    (hk : ((p ^ n : ℕ) : ZMod (p ^ (n + 1))) * k ≠ 0) :
    𝓕 (fun y => g ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) y)) k = 0 := by
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  have hc0 : (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)))
        ((p ^ n : ℕ) : ZMod (p ^ (n + 1))) = 0 := by
    rw [map_natCast, ZMod.natCast_self]
  have hper : ∀ y : ZMod (p ^ (n + 1)),
      g ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)))
          (y + ((p ^ n : ℕ) : ZMod (p ^ (n + 1)))))
      = g ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) y) := by
    intro y
    rw [map_add, hc0, add_zero]
  have hchar : stdAddChar (-(((p ^ n : ℕ) : ZMod (p ^ (n + 1))) * k)) ≠ 1 := by
    rw [ne_eq, IsPrimitive.zmod_char_eq_one_iff (p ^ (n + 1))
        (isPrimitive_stdAddChar (p ^ (n + 1))), neg_eq_zero]
    exact hk
  exact dft_eq_zero_of_period _ ((p ^ n : ℕ) : ZMod (p ^ (n + 1))) k hper hchar

/-- Support form of the intertwiner: the spectrum of a coarse (`castHom`-pulled-back)
function is contained in the `p`-divisible band `{k | ↑(p^n) * k = 0}`. -/
theorem dft_pullback_support {p n : ℕ} [Fact p.Prime]
    (g : ZMod (p ^ n) → ℂ) (k : ZMod (p ^ (n + 1)))
    (hk : 𝓕 (fun y => g ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) y)) k ≠ 0) :
    ((p ^ n : ℕ) : ZMod (p ^ (n + 1))) * k = 0 := by
  by_contra h
  exact hk (dft_pullback_eq_zero_of_band g k h)

/-! ### The p-adic frequency ladder: the dimension staircase

We bundle the coarse functions into the filtration `V₀ ⊆ V₁ ⊆ ⋯ ⊆ V_N = ℂ[ZMod pᴺ]`,
where `Vₙ` is the image of pullback along the residue map `ZMod pᴺ → ZMod pⁿ`
(equivalently, by `periodic_iff_dft_eq_zero_off_band`, the functions whose spectrum lives
in the bottom `n` bands).  We prove `dim Vₙ = pⁿ`, so the `n`-th band `Wₙ = Vₙ ⊖ Vₙ₋₁`
has dimension `pⁿ⁻¹(p − 1)`: refining the scale switches on exactly one rung at a time. -/

/-- The level-`n` **coarse subspace** of `ℂ[ZMod pᴺ]`: functions pulled back along the
residue map `castHom : ZMod pᴺ → ZMod pⁿ`.  By the intertwiner these are exactly the
functions band-limited to the bottom `n` frequency bands. -/
noncomputable def coarseSubspace (p N n : ℕ) (h : n ≤ N) :
    Submodule ℂ (ZMod (p ^ N) → ℂ) :=
  LinearMap.range
    (LinearMap.funLeft ℂ ℂ (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))))

/-- **Dimension of the `n`-th rung:** `dim Vₙ = pⁿ`.
The pullback along the surjective residue map is injective, so `Vₙ ≅ ℂ[ZMod pⁿ]`. -/
theorem finrank_coarseSubspace (p N n : ℕ) [Fact p.Prime] (h : n ≤ N) :
    Module.finrank ℂ (coarseSubspace p N n h) = p ^ n := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  unfold coarseSubspace
  rw [LinearMap.finrank_range_of_inj
        (LinearMap.funLeft_injective_of_surjective ℂ ℂ _
          (ZMod.castHom_surjective (pow_dvd_pow p h))),
      Module.finrank_fintype_fun_eq_card, ZMod.card]

/-- **The ladder is a filtration:** `Vₘ ⊆ Vₙ` whenever `m ≤ n`.
Coarser pullbacks factor through finer ones (`castHom` composition). -/
theorem coarseSubspace_mono (p N m n : ℕ) (hmn : m ≤ n) (hnN : n ≤ N) :
    coarseSubspace p N m (hmn.trans hnN) ≤ coarseSubspace p N n hnN := by
  have hcomp :
      ((ZMod.castHom (pow_dvd_pow p (hmn.trans hnN)) (ZMod (p ^ m)) :
            ZMod (p ^ N) →+* ZMod (p ^ m)) : ZMod (p ^ N) → ZMod (p ^ m))
        = (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)) : ZMod (p ^ n) →+* ZMod (p ^ m))
            ∘ (ZMod.castHom (pow_dvd_pow p hnN) (ZMod (p ^ n)) :
                ZMod (p ^ N) →+* ZMod (p ^ n)) := by
    rw [← RingHom.coe_comp]
    congr 1
    exact RingHom.ext_zmod _ _
  unfold coarseSubspace
  rw [hcomp, LinearMap.funLeft_comp]
  exact LinearMap.range_comp_le_range _ _

/-- **Band dimension:** the band `Wₙ₊₁ = Vₙ₊₁ ⊖ Vₙ` has dimension `pⁿ(p − 1)`.
Each new scale switches on exactly one band; the bands partition the spectrum, recovering
`∑ₙ pⁿ⁻¹(p−1) = pᴺ − 1` non-constant modes plus the constant. -/
theorem bandDim (p N n : ℕ) [Fact p.Prime] (h : n + 1 ≤ N) :
    Module.finrank ℂ (coarseSubspace p N (n + 1) h)
        - Module.finrank ℂ (coarseSubspace p N n ((Nat.le_succ n).trans h))
      = p ^ n * (p - 1) := by
  rw [finrank_coarseSubspace, finrank_coarseSubspace]
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have key : p ^ (n + 1) = p ^ n * (p - 1) + p ^ n := by
    calc p ^ (n + 1) = p ^ n * p := pow_succ p n
      _ = p ^ n * ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp]
      _ = p ^ n * (p - 1) + p ^ n := by rw [mul_add, mul_one]
  omega

end SGC.Bridge
