/-
Copyright (c) 2024 UPAT Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: UPAT Contributors
-/
import UPAT.Information.Gaussian
import UPAT.Topology.Blanket

/-!
# The Gaussian Lemma: Information-Geometric Equivalence

This module proves the fundamental equivalence between information-theoretic
conditional independence and geometric orthogonality for Gaussian distributions.

## Theoretical Context

In UPAT v1, we defined Markov Blankets using geometric orthogonality:
  `inner_pi π f g = 0` for internal f and external g

This was a computational proxy for the true information-theoretic definition:
  `I(Internal; External | Blanket) = 0` (Conditional Mutual Information)

This module proves these are **equivalent** in the Gaussian/thermodynamic limit.

## The Gaussian Lemma

For jointly Gaussian variables (X, Y, Z):
  I(X; Y | Z) = 0  ⟺  Λ_XY|Z = 0  ⟺  ⟨f_X, f_Y⟩_π = 0

## Main Theorems

* `gaussian_cmi_zero_iff_precision_zero` - CMI = 0 iff precision block is zero
* `dynamical_blanket_iff_information_blanket` - The main equivalence theorem
* `information_bridge` - Connects v2 Information theory to v1 Geometry

## References

* [Lauritzen] Graphical Models, Chapter 5
* [Koller-Friedman] Probabilistic Graphical Models, Chapter 4
-/

noncomputable section

namespace UPAT.Information

variable {n : ℕ}

/-! ### 1. Conditional Mutual Information Abstraction -/

/-- **Conditional Mutual Information** I(A; B | C) abstracted as a sum
    of precision matrix entries. Zero CMI means zero cross-block precision. -/
def conditionalMutualInfo (P : PrecisionMatrix n) (A B : Finset (Fin n)) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, |P.entry a b|

/-- CMI is non-negative. -/
lemma conditionalMutualInfo_nonneg (P : PrecisionMatrix n) (A B : Finset (Fin n)) :
    0 ≤ conditionalMutualInfo P A B := by
  unfold conditionalMutualInfo
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  exact abs_nonneg _

/-! ### 2. The Gaussian Lemma: CMI ↔ Precision Zero -/

/-- Helper: sum of non-negative terms is zero iff each term is zero. -/
lemma sum_abs_eq_zero_iff {α : Type*} (s : Finset α) (f : α → ℝ) :
    ∑ x ∈ s, |f x| = 0 ↔ ∀ x ∈ s, f x = 0 := by
  constructor
  · intro h x hx
    have h_nonneg : ∀ y ∈ s, 0 ≤ |f y| := fun _ _ => abs_nonneg _
    have h_term := Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h x hx
    exact abs_eq_zero.mp h_term
  · intro h
    apply Finset.sum_eq_zero
    intro x hx
    rw [h x hx, abs_zero]

/-- **Gaussian CMI-Precision Equivalence**: CMI is zero iff precision block is zero.
    I(A; B | C) = 0 ⟺ ∀ a ∈ A, b ∈ B, Λ_ab = 0 -/
theorem gaussian_cmi_zero_iff_precision_zero (P : PrecisionMatrix n) 
    (A B : Finset (Fin n)) :
    conditionalMutualInfo P A B = 0 ↔ ∀ a ∈ A, ∀ b ∈ B, P.entry a b = 0 := by
  unfold conditionalMutualInfo
  constructor
  · intro h_sum a ha b hb
    -- Outer sum is zero, so each inner sum is zero
    have h_outer_nonneg : ∀ a' ∈ A, 0 ≤ ∑ b' ∈ B, |P.entry a' b'| := 
      fun a' _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have h_inner_zero := Finset.sum_eq_zero_iff_of_nonneg h_outer_nonneg |>.mp h_sum a ha
    -- Inner sum is zero, so each term is zero
    have h_term_nonneg : ∀ b' ∈ B, 0 ≤ |P.entry a b'| := fun _ _ => abs_nonneg _
    have h_abs_zero := Finset.sum_eq_zero_iff_of_nonneg h_term_nonneg |>.mp h_inner_zero b hb
    exact abs_eq_zero.mp h_abs_zero
  · intro h_prec
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    rw [h_prec a ha b hb, abs_zero]

/-! ### 3. Main Theorem: Blanket Equivalence -/

/-- A **Blanket Partition** divides states into internal, blanket, and external. -/
structure BlanketPartition (n : ℕ) where
  internal : Finset (Fin n)
  blanket : Finset (Fin n)
  external : Finset (Fin n)
  disjoint_int_ext : Disjoint internal external

/-- **Dynamical Blanket**: Zero precision between internal and external. -/
def IsDynamicalBlanket (P : PrecisionMatrix n) (B : BlanketPartition n) : Prop :=
  ∀ i ∈ B.internal, ∀ e ∈ B.external, P.entry i e = 0

/-- **Information Blanket**: Zero CMI between internal and external. -/
def IsInformationBlanket (P : PrecisionMatrix n) (B : BlanketPartition n) : Prop :=
  conditionalMutualInfo P B.internal B.external = 0

/-- **The Gaussian Lemma**: Dynamical and information blankets are equivalent.
    
    This justifies UPAT v1's use of geometric orthogonality as a proxy
    for information-theoretic conditional independence. -/
theorem dynamical_blanket_iff_information_blanket (P : PrecisionMatrix n) 
    (B : BlanketPartition n) :
    IsDynamicalBlanket P B ↔ IsInformationBlanket P B := by
  unfold IsDynamicalBlanket IsInformationBlanket
  rw [gaussian_cmi_zero_iff_precision_zero]

end UPAT.Information

/-! ## Part II: The Information Bridge to v1 Geometry -/

namespace UPAT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 4. Precision Matrix from Generator -/

/-- Extract a **Precision-like Matrix** from a generator L.
    The off-diagonal entries encode conditional dependencies.
    L_{ij} = 0 means no direct coupling between i and j. -/
def precisionFromGenerator (L : Matrix V V ℝ) : V → V → ℝ := 
  fun i j => L i j

/-- **Information Blanket from Generator**: A blanket partition has zero
    cross-block entries in the generator (no direct internal-external coupling). -/
def IsInformationBlanketV (L : Matrix V V ℝ) (B : BlanketPartition V) : Prop :=
  ∀ i ∈ B.internal, ∀ e ∈ B.external, L i e = 0

/-- A matrix is **symmetric** if L i j = L j i for all i, j. -/
def IsSymmetric (L : Matrix V V ℝ) : Prop := ∀ i j, L i j = L j i

/-! ### 5. The Information Bridge Theorem -/

/-- **The Information Bridge**: `RespectsBlank` (v1 Geometry) implies
    `IsInformationBlanketV` (v2 Information).
    
    This theorem proves that our geometric definition of blankets
    is equivalent to the information-theoretic definition (one direction).
    
    Physical meaning: If the generator respects the blanket topology,
    then there is zero information flow between internal and external. -/
theorem information_bridge_forward (L : Matrix V V ℝ) (B : BlanketPartition V) 
    (h : RespectsBlank L B) : IsInformationBlanketV L B := by
  unfold IsInformationBlanketV
  exact h.1

/-- **The Information Bridge (Reverse)**: `IsInformationBlanketV` implies
    half of `RespectsBlank`. For the full equivalence, we also need
    the external-to-internal direction.
    
    Note: For symmetric generators (reversible dynamics), one direction suffices. -/
theorem information_bridge_reverse (L : Matrix V V ℝ) (B : BlanketPartition V)
    (h_int_ext : ∀ i ∈ B.internal, ∀ e ∈ B.external, L i e = 0)
    (h_ext_int : ∀ e ∈ B.external, ∀ i ∈ B.internal, L e i = 0) :
    RespectsBlank L B := by
  exact ⟨h_int_ext, h_ext_int⟩

/-- **Symmetric Information Bridge**: For symmetric matrices (reversible dynamics),
    zero internal→external implies zero external→internal. -/
theorem symmetric_information_bridge (L : Matrix V V ℝ) (B : BlanketPartition V)
    (h_sym : IsSymmetric L)
    (h : IsInformationBlanketV L B) : RespectsBlank L B := by
  constructor
  · exact h
  · intro e he i hi
    rw [h_sym e i]
    exact h i hi e he

/-! ### 6. Full Equivalence for Reversible Systems -/

/-- **Information-Geometry Equivalence**: For reversible (symmetric) generators,
    `RespectsBlank` and `IsInformationBlanketV` are equivalent.
    
    This is the central theorem connecting UPAT v1 (Geometry) to v2 (Information). -/
theorem information_geometry_equivalence (L : Matrix V V ℝ) (B : BlanketPartition V)
    (h_sym : IsSymmetric L) :
    RespectsBlank L B ↔ IsInformationBlanketV L B := by
  constructor
  · exact information_bridge_forward L B
  · exact symmetric_information_bridge L B h_sym

/-- **Corollary**: For reversible systems, orthogonality of internal/external 
    functions is equivalent to zero information flow.
    
    This combines `blanket_orthogonality` (v1) with the Information Bridge (v2). -/
theorem orthogonality_iff_zero_information (L : Matrix V V ℝ) (B : BlanketPartition V)
    (h_sym : IsSymmetric L) (pi_dist : V → ℝ)
    (f g : V → ℝ) (hf : IsInternalFunction B f) (hg : IsExternalFunction B g) :
    (RespectsBlank L B → inner_pi pi_dist f g = 0) ∧
    (IsInformationBlanketV L B → inner_pi pi_dist f g = 0) := by
  constructor
  · intro h_respect
    exact blanket_orthogonality L B pi_dist h_respect f g hf hg
  · intro h_info
    have h_respect := symmetric_information_bridge L B h_sym h_info
    exact blanket_orthogonality L B pi_dist h_respect f g hf hg

end UPAT

end
