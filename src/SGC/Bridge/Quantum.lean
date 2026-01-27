/-
Copyright (c) 2026 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Formalization Team
-/
import SGC.Axioms.GeometryGeneral
import SGC.Spectral.Core.Assumptions
import SGC.Renormalization.Approximate

/-!
# Quantum Bridge: Classical-Quantum Dictionary

This file establishes the formal correspondence between classical Markov chain
theory and quantum information theory. The key insight is that lumpability
(coarse-graining that preserves Markov structure) corresponds to quantum error
correction (encoding that preserves quantum information).

## Main Correspondences

| Classical (Markov)              | Quantum                              |
|---------------------------------|--------------------------------------|
| Probability distribution π      | Density matrix ρ                     |
| Stochastic matrix P             | Quantum channel (CPTP map) Φ         |
| Generator L (= P - I)           | Lindbladian ℒ                        |
| Partition of state space        | Projection onto code subspace        |
| Lumpability (exact)             | Knill-Laflamme conditions (ε = 0)    |
| Approximate lumpability         | Approximate QEC                      |
| Spectral gap γ                  | Lindbladian gap γ_L                  |
| Mixing time τ_mix               | Decoherence time T_2                 |

## References

* [Knill-Laflamme 1997] Theory of quantum error-correcting codes
* [Lindblad 1976] On the generators of quantum dynamical semigroups
* [Kempe et al. 2001] Quantum random walks

-/

noncomputable section

namespace SGC
namespace Bridge
namespace Quantum

open Finset
open SGC.Axioms.GeometryGeneral
open SGC.Spectral
open SGC.Approximate

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## Classical Objects

We first recall the classical objects from SGC that will be bridged to quantum. -/

/-- A classical state is a probability distribution over V. -/
structure ClassicalState (V : Type*) [Fintype V] where
  dist : V → ℝ
  nonneg : ∀ v, 0 ≤ dist v
  sum_one : ∑ v, dist v = 1

/-- A classical generator is a rate matrix (rows sum to 0, off-diagonal nonneg). -/
structure ClassicalGenerator (V : Type*) [Fintype V] where
  L : Matrix V V ℝ
  row_sum_zero : ∀ i, ∑ j, L i j = 0
  off_diag_nonneg : ∀ i j, i ≠ j → 0 ≤ L i j

/-! ## Quantum Objects

Quantum objects use complex scalars and the Hermitian inner product from GeometryGeneral. -/

/-- A quantum state (density matrix) is a positive semidefinite operator with trace 1.
    We use ℂ as the scalar field for quantum mechanics. -/
abbrev QuantumState (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ) :=
  { ρ : (V → ℂ) →ₗ[ℂ] (V → ℂ) // IsDensityMatrix pi_dist ρ }

/-- A Lindbladian is the generator of a quantum dynamical semigroup.
    It takes the form ℒ(ρ) = -i[H,ρ] + Σ_k (L_k ρ L_k† - ½{L_k†L_k, ρ})
    where H is Hermitian and L_k are jump operators. -/
structure Lindbladian (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ) where
  /-- The superoperator acting on density matrices -/
  superop : ((V → ℂ) →ₗ[ℂ] (V → ℂ)) →ₗ[ℂ] ((V → ℂ) →ₗ[ℂ] (V → ℂ))
  /-- Trace-preserving: Tr(ℒ(ρ)) = 0 for all ρ -/
  trace_preserving : ∀ ρ, trace_pi pi_dist (superop ρ) = 0
  /-- Complete positivity (CPTP property, axiomatized) -/
  cptp : True  -- Placeholder; full CPTP requires Kraus representation

/-! ## Code Subspace and Projections

The quantum analog of a partition is a projection onto a code subspace.
Error correction works by projecting back onto this subspace. -/

/-- A code subspace is defined by a projection operator. -/
structure CodeSubspace (V : Type*) [Fintype V] [DecidableEq V] (pi_dist : V → ℝ) where
  /-- The projector onto the code subspace -/
  proj : (V → ℂ) →ₗ[ℂ] (V → ℂ)
  /-- Projector is self-adjoint -/
  self_adjoint : IsSelfAdjoint_pi pi_dist proj
  /-- Projector satisfies P² = P -/
  idempotent : proj ∘ₗ proj = proj

/-! ## Knill-Laflamme Conditions

The Knill-Laflamme conditions characterize when a code can perfectly correct
a set of errors. This is the quantum analog of exact lumpability. -/

/-- Error operators are the quantum analog of "leakage" in approximate lumpability. -/
structure ErrorOperators (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) where
  /-- Set of error operators {E_k} -/
  errors : Fin n → ((V → ℂ) →ₗ[ℂ] (V → ℂ))

/-- The Knill-Laflamme conditions: P E_i† E_j P = α_ij P for some scalars α_ij.
    When satisfied, errors can be perfectly corrected.

    This is the quantum error correction condition: the projection of error
    compositions back onto the code subspace is proportional to the projector itself,
    meaning errors don't distinguish between codewords. -/
def KnillLaflamme (pi_dist : V → ℝ) (code : CodeSubspace V pi_dist)
    {n : ℕ} (errors : ErrorOperators V n) : Prop :=
  ∃ (α : Fin n → Fin n → ℂ), ∀ (i : Fin n) (j : Fin n),
    code.proj ∘ₗ (adjoint_pi pi_dist (errors.errors i)) ∘ₗ (errors.errors j) ∘ₗ code.proj =
    α i j • code.proj

/-! ## The Bridge: Lumpability ↔ Quantum Error Correction

This is the central theorem establishing the equivalence between classical
lumpability and quantum error correction. -/

/-- Embed a classical state as a diagonal quantum state. -/
def embedClassical (pi_dist : V → ℝ) (s : ClassicalState V) :
    (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  { toFun := fun v => fun x => (s.dist x : ℂ) * v x
    map_add' := fun u v => by ext x; simp [mul_add]
    map_smul' := fun c v => by ext x; simp [mul_comm, mul_assoc] }

/-- The embedding of a classical state is a valid quantum state. -/
axiom embedClassical_isDensityMatrix (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (s : ClassicalState V) :
    IsDensityMatrix pi_dist (embedClassical pi_dist s)

/-- Convert a classical partition to a code subspace projector.
    Each partition block becomes a basis vector in the code subspace. -/
axiom partitionToCodeSubspace (pi_dist : V → ℝ) (P : Partition V) :
    CodeSubspace V pi_dist

/-- The code projector from a partition corresponds to the complexified coarse projector.
    This is the key structural link between classical and quantum pictures. -/
axiom partitionToCodeSubspace_proj_eq (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (P : Partition V) :
    ∀ f : V → ℂ, (partitionToCodeSubspace pi_dist P).proj f =
      fun v => (CoarseProjector P pi_dist hπ (fun w => RCLike.re (f w)) v : ℂ) +
               Complex.I * (CoarseProjector P pi_dist hπ (fun w => RCLike.im (f w)) v : ℂ)

/-- Lift a real matrix to act on complex-valued functions.
    (L_ℂ f)(v) = Σ_w L(v,w) · f(w) -/
def matrixToLinearMapComplex (L : Matrix V V ℝ) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun f v := ∑ w, (L v w : ℂ) * f w
  map_add' f g := by
    ext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr 1; ext w; ring
  map_smul' c f := by
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    congr 1; ext w; ring

/-- The defect operator from approximate lumpability corresponds to
    the error syndrome in quantum error correction.

    For a classical generator L and partition P, the defect D = (I - Π) L Π
    becomes the single error operator in the quantum picture.

    **CONSTRUCTIVE DEFINITION**: D = (I - Π) ∘ L_ℂ ∘ Π
    This allows structural properties to be proven by algebraic simplification. -/
def complexifyDefect (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  let proj := (partitionToCodeSubspace pi_dist P).proj
  (LinearMap.id - proj) ∘ₗ (matrixToLinearMapComplex L) ∘ₗ proj

/-- The complexified defect is zero iff the real defect has zero operator norm. -/
axiom complexifyDefect_zero_iff (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    complexifyDefect pi_dist hπ L P = 0 ↔ opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0

/-! ### Structural Properties of Partition-Derived Codes

The key insight for deriving the KL-Lumpability equivalence is that defect operators
have special orthogonality structure: D = (I-Π)LΠ maps code vectors to the orthogonal
complement. This structural constraint forces the KL coefficient α to be zero. -/

/-- **Structural Property 1a**: The complexified defect maps code subspace to its complement.
    This follows from D = (I-Π)LΠ, so P D P = P(I-Π)LΠP = 0 (since P(I-Π) = 0).

    **PROVEN BY DEFINITION**: D = (I-Π) L Π, so
    Π D Π = Π (I-Π) L Π Π = Π (I-Π) L Π (by idempotence)
                           = (Π - Π²) L Π = (Π - Π) L Π = 0 -/
theorem complexifyDefect_orthogonal (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    (partitionToCodeSubspace pi_dist P).proj ∘ₗ
    (complexifyDefect pi_dist hπ L P) ∘ₗ
    (partitionToCodeSubspace pi_dist P).proj = 0 := by
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let L_c := matrixToLinearMapComplex L
  -- D = (I - proj) ∘ L_c ∘ proj by definition
  have h_def : complexifyDefect pi_dist hπ L P = (LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj := rfl
  -- proj is idempotent: proj ∘ proj = proj
  have h_idem : proj ∘ₗ proj = proj := (partitionToCodeSubspace pi_dist P).idempotent
  -- proj D proj = proj (I - proj) L_c proj proj = proj (I - proj) L_c proj
  -- proj (I - proj) = proj - proj² = proj - proj = 0
  have h_proj_annihilate : proj ∘ₗ (LinearMap.id - proj) = 0 := by
    rw [LinearMap.comp_sub, LinearMap.comp_id, h_idem, sub_self]
  calc proj ∘ₗ (complexifyDefect pi_dist hπ L P) ∘ₗ proj
      = proj ∘ₗ ((LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj) ∘ₗ proj := by rw [h_def]
    _ = (proj ∘ₗ (LinearMap.id - proj)) ∘ₗ L_c ∘ₗ (proj ∘ₗ proj) := by
        simp only [LinearMap.comp_assoc]
    _ = 0 ∘ₗ L_c ∘ₗ proj := by rw [h_proj_annihilate, h_idem]
    _ = 0 := by simp only [LinearMap.zero_comp]

/-- **Structural Property 1b**: The defect kills the complement of the code subspace.
    This follows from D = (I-Π)LΠ, so D(I-Π) = (I-Π)LΠ(I-Π) = 0 (since Π(I-Π) = 0).

    **PROVEN BY DEFINITION**: D = (I-Π) L Π, so
    D (I-Π) = (I-Π) L Π (I-Π) = (I-Π) L (Π - Π²) = (I-Π) L 0 = 0 -/
theorem complexifyDefect_kills_complement (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    (complexifyDefect pi_dist hπ L P) ∘ₗ
    (LinearMap.id - (partitionToCodeSubspace pi_dist P).proj) = 0 := by
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let L_c := matrixToLinearMapComplex L
  -- D = (I - proj) ∘ L_c ∘ proj by definition
  have h_def : complexifyDefect pi_dist hπ L P = (LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj := rfl
  -- proj is idempotent: proj ∘ proj = proj
  have h_idem : proj ∘ₗ proj = proj := (partitionToCodeSubspace pi_dist P).idempotent
  -- proj (I - proj) = proj - proj² = proj - proj = 0
  have h_proj_comp : proj ∘ₗ (LinearMap.id - proj) = 0 := by
    simp only [LinearMap.comp_sub, LinearMap.comp_id, h_idem, sub_self]
  -- D (I-proj) = (I-proj) L_c proj (I-proj) = (I-proj) L_c (proj - proj²) = (I-proj) L_c 0 = 0
  calc (complexifyDefect pi_dist hπ L P) ∘ₗ (LinearMap.id - proj)
      = ((LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj) ∘ₗ (LinearMap.id - proj) := by rw [h_def]
    _ = (LinearMap.id - proj) ∘ₗ L_c ∘ₗ (proj ∘ₗ (LinearMap.id - proj)) := by simp only [LinearMap.comp_assoc]
    _ = (LinearMap.id - proj) ∘ₗ L_c ∘ₗ 0 := by rw [h_proj_comp]
    _ = 0 := by simp only [LinearMap.comp_zero]

/-- **Structural Property 1c**: P E† P = 0 follows from P E P = 0.

    **PROVEN**: Taking adjoint of P E P = 0:
    - (P ∘ E ∘ P)† = P† ∘ E† ∘ P† (by `adjoint_pi_comp` twice)
    - = P ∘ E† ∘ P (since P is self-adjoint: P† = P)
    - = (P E P)† = 0† = 0 (by `adjoint_pi_zero`)

    This is a key step for proving that the KL condition forces α = 0. -/
theorem adjoint_defect_orthogonal (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    (partitionToCodeSubspace pi_dist P).proj ∘ₗ
    (adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P)) ∘ₗ
    (partitionToCodeSubspace pi_dist P).proj = 0 := by
  -- Get P E P = 0
  have h_PEP := complexifyDefect_orthogonal pi_dist hπ L P
  -- Get P is self-adjoint: P† = P
  have h_P_sa := (partitionToCodeSubspace pi_dist P).self_adjoint
  unfold SGC.Axioms.GeometryGeneral.IsSelfAdjoint_pi at h_P_sa
  -- Abbreviations
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let E := complexifyDefect pi_dist hπ L P
  -- (P E P)† = 0† = 0
  have h_adj_zero := SGC.Axioms.GeometryGeneral.adjoint_pi_zero (𝕜 := ℂ) pi_dist
  -- The adjoint of P E P using composition rule
  have h_comp1 : adjoint_pi pi_dist (E ∘ₗ proj) =
      (adjoint_pi pi_dist proj) ∘ₗ (adjoint_pi pi_dist E) :=
    SGC.Axioms.GeometryGeneral.adjoint_pi_comp pi_dist E proj
  have h_comp2 : adjoint_pi pi_dist (proj ∘ₗ E ∘ₗ proj) =
      (adjoint_pi pi_dist (E ∘ₗ proj)) ∘ₗ (adjoint_pi pi_dist proj) :=
    SGC.Axioms.GeometryGeneral.adjoint_pi_comp pi_dist proj (E ∘ₗ proj)
  -- Substitute P† = P
  simp only [h_P_sa] at h_comp1 h_comp2
  -- (P E P)† = (E P)† ∘ P = (P ∘ E†) ∘ P = P ∘ E† ∘ P
  rw [h_comp1] at h_comp2
  -- P E P = 0, so (P E P)† = 0† = 0
  have h_adj_PEP : adjoint_pi pi_dist (proj ∘ₗ E ∘ₗ proj) = 0 := by
    rw [h_PEP, h_adj_zero]
  -- Therefore P E† P = 0
  rw [h_comp2, h_P_sa] at h_adj_PEP
  exact h_adj_PEP

/-- **Structural Property 2**: The inner product of E†E ψ with ψ equals ‖Eψ‖².
    This is standard: ⟨E†E ψ, ψ⟩ = ⟨Eψ, Eψ⟩ = ‖Eψ‖².

    **PROVEN** from adjoint_pi_spec: ⟨A†u, v⟩ = ⟨u, Av⟩, setting u = Eψ, v = ψ. -/
theorem inner_adjoint_self (pi_dist : V → ℝ) (E : (V → ℂ) →ₗ[ℂ] (V → ℂ)) (ψ : V → ℂ) :
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist (adjoint_pi pi_dist E (E ψ)) ψ =
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist (E ψ) (E ψ) := by
  -- Use adjoint_pi_spec: ⟨A†u, v⟩ = ⟨u, Av⟩
  -- With A = E, u = Eψ, v = ψ: ⟨E†(Eψ), ψ⟩ = ⟨Eψ, Eψ⟩
  exact SGC.Axioms.GeometryGeneral.adjoint_pi_spec pi_dist E (E ψ) ψ

/-- **Structural Property 3**: An operator is zero iff its norm squared is zero on all inputs.
    More precisely: E = 0 ↔ ∀ ψ, ⟨Eψ, Eψ⟩ = 0. -/
axiom operator_zero_iff_norm_sq_zero (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (E : (V → ℂ) →ₗ[ℂ] (V → ℂ)) :
    E = 0 ↔ ∀ ψ, SGC.Axioms.GeometryGeneral.inner_pi pi_dist (E ψ) (E ψ) = 0

/-- **Lemma 3a**: KL coefficient reality from self-adjoint operator.

    For the KL condition P E† E P = α P, the coefficient α must be real.

    **Proof**: For any codeword ψ (with P ψ = ψ and ⟨ψ, ψ⟩ > 0):
    1. Take inner product of KL equation with ψ: ⟨P E† E P ψ, ψ⟩ = α·⟨P ψ, ψ⟩
    2. Since P is self-adjoint and P ψ = ψ: ⟨E† E ψ, ψ⟩ = α·⟨ψ, ψ⟩
    3. E†E is self-adjoint, so ⟨E†E ψ, ψ⟩ is real (by inner_self_adjoint_real)
    4. ⟨ψ, ψ⟩ is real and positive (norm squared of non-zero vector)
    5. Therefore α = (real) / (positive real) is real, so Im(α) = 0 -/
axiom KL_coefficient_real (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (α : ℂ)
    (h_sa : SGC.Axioms.GeometryGeneral.IsSelfAdjoint_pi pi_dist
        (adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P) ∘ₗ
         complexifyDefect pi_dist hπ L P))
    (hKL : ∀ f, (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
        α • ((partitionToCodeSubspace pi_dist P).proj f)) :
    α.im = 0

/-- **Structural Property 4**: The projection is self-adjoint w.r.t. the weighted inner product.
    This follows from the projection being orthogonal in the π-weighted sense.

    **PROVEN** from CodeSubspace.self_adjoint field and isSelfAdjoint_pi_iff. -/
theorem codeSubspace_proj_selfAdjoint (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (P : Partition V) (ψ φ : V → ℂ) :
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist
      ((partitionToCodeSubspace pi_dist P).proj ψ) φ =
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist
      ψ ((partitionToCodeSubspace pi_dist P).proj φ) := by
  -- partitionToCodeSubspace returns a CodeSubspace with self_adjoint field
  have h_sa := (partitionToCodeSubspace pi_dist P).self_adjoint
  -- Use isSelfAdjoint_pi_iff to get the inner product characterization
  exact (SGC.Axioms.GeometryGeneral.isSelfAdjoint_pi_iff pi_dist hπ _).mp h_sa ψ φ

/-- **Structural Property 5**: Orthogonal decomposition of the inner product.
    For orthogonal projection P: ⟨ψ, ψ⟩ = ⟨Pψ, Pψ⟩ + ⟨(I-P)ψ, (I-P)ψ⟩.

    **Proof path**: Use ψ = Pψ + (ψ - Pψ), expand via linearity, and show cross
    terms vanish because P(ψ - Pψ) = 0 (by idempotence) and P is self-adjoint:
    ⟨Pψ, ψ - Pψ⟩ = ⟨ψ, P(ψ - Pψ)⟩ = ⟨ψ, 0⟩ = 0. -/
axiom inner_pi_orthogonal_decomp (pi_dist : V → ℝ) (P : Partition V) (ψ : V → ℂ) :
    let proj := (partitionToCodeSubspace pi_dist P).proj
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist ψ ψ =
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist (proj ψ) (proj ψ) +
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist (ψ - proj ψ) (ψ - proj ψ)

/-- **Lemma 6a**: For codewords, the KL condition gives ‖Eψ‖² = α‖ψ‖².

    **PROVEN**: For codeword ψ (Pψ = ψ):
    1. KL says P E† E P ψ = α ψ
    2. Take ⟨_, ψ⟩: ⟨P E† E ψ, ψ⟩ = α⟨ψ, ψ⟩
    3. P self-adjoint: ⟨E† E ψ, Pψ⟩ = ⟨E† E ψ, ψ⟩
    4. inner_adjoint_self: ⟨E† E ψ, ψ⟩ = ⟨Eψ, Eψ⟩ = ‖Eψ‖²

    Note: We use real α (physically, the leakage coefficient must be real). -/
theorem KL_gives_norm_sq_proportional (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (α : ℝ)
    (hKL : ∀ f, (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
        (α : ℂ) • ((partitionToCodeSubspace pi_dist P).proj f))
    (ψ : V → ℂ) (h_codeword : (partitionToCodeSubspace pi_dist P).proj ψ = ψ) :
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist
      ((complexifyDefect pi_dist hπ L P) ψ) ((complexifyDefect pi_dist hπ L P) ψ) =
    (α : ℂ) * SGC.Axioms.GeometryGeneral.inner_pi pi_dist ψ ψ := by
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let E := complexifyDefect pi_dist hπ L P
  -- KL condition for ψ: P E† E (Pψ) = α (Pψ) = α ψ
  have h_KL_ψ := hKL ψ
  rw [h_codeword] at h_KL_ψ
  -- Take inner product with ψ: ⟨P E† E ψ, ψ⟩ = ⟨α ψ, ψ⟩ = α⟨ψ, ψ⟩
  -- For real α: star α = α, so inner_pi_smul_left gives α * inner
  have h_inner_RHS : SGC.Axioms.GeometryGeneral.inner_pi pi_dist ((α : ℂ) • ψ) ψ =
      (α : ℂ) * SGC.Axioms.GeometryGeneral.inner_pi pi_dist ψ ψ := by
    rw [SGC.Axioms.GeometryGeneral.inner_pi_smul_left]
    -- star (α : ℂ) = α for real α (α has zero imaginary part)
    congr 1
    simp only [RCLike.star_def, Complex.conj_ofReal]
  -- LHS: ⟨P E† E ψ, ψ⟩ = ⟨E† E ψ, Pψ⟩ = ⟨E† E ψ, ψ⟩ (P self-adjoint, Pψ = ψ)
  have h_inner_LHS : SGC.Axioms.GeometryGeneral.inner_pi pi_dist (proj (adjoint_pi pi_dist E (E ψ))) ψ =
      SGC.Axioms.GeometryGeneral.inner_pi pi_dist (adjoint_pi pi_dist E (E ψ)) ψ := by
    rw [codeSubspace_proj_selfAdjoint pi_dist hπ P (adjoint_pi pi_dist E (E ψ)) ψ]
    rw [h_codeword]
  -- By inner_adjoint_self: ⟨E† E ψ, ψ⟩ = ⟨Eψ, Eψ⟩
  have h_adj_self := inner_adjoint_self pi_dist E ψ
  -- Chain: ⟨P E† E ψ, ψ⟩ = ⟨E† E ψ, ψ⟩ = ⟨Eψ, Eψ⟩ = α⟨ψ, ψ⟩
  calc SGC.Axioms.GeometryGeneral.inner_pi pi_dist (E ψ) (E ψ)
    = SGC.Axioms.GeometryGeneral.inner_pi pi_dist (adjoint_pi pi_dist E (E ψ)) ψ := h_adj_self.symm
    _ = SGC.Axioms.GeometryGeneral.inner_pi pi_dist (proj (adjoint_pi pi_dist E (E ψ))) ψ := h_inner_LHS.symm
    _ = SGC.Axioms.GeometryGeneral.inner_pi pi_dist ((α : ℂ) • ψ) ψ := by rw [h_KL_ψ]
    _ = (α : ℂ) * SGC.Axioms.GeometryGeneral.inner_pi pi_dist ψ ψ := h_inner_RHS

/-- **Lemma 6b**: The defect operator E = (I-P)LP factors as E = (I-P) ∘ E.
    This means E maps everything to the complement of the code subspace.

    **PROVEN BY DEFINITION**: E = (I-P) L P, so
    (I-P) ∘ E = (I-P) ∘ (I-P) L P = (I-P) L P = E
    since (I-P) is idempotent (because P is idempotent).

    Combined with P E† P = 0 (`adjoint_defect_orthogonal`), for partition codes
    the uniform leakage condition forces α = 0. -/
theorem defect_maps_to_complement (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) :
    (complexifyDefect pi_dist hπ L P) =
    (LinearMap.id - (partitionToCodeSubspace pi_dist P).proj) ∘ₗ
    (complexifyDefect pi_dist hπ L P) := by
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let L_c := matrixToLinearMapComplex L
  -- E = (I - proj) ∘ L_c ∘ proj by definition
  have h_def : complexifyDefect pi_dist hπ L P = (LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj := rfl
  -- proj is idempotent, so (I - proj) is also idempotent
  have h_idem : proj ∘ₗ proj = proj := (partitionToCodeSubspace pi_dist P).idempotent
  have h_complement_idem : (LinearMap.id - proj) ∘ₗ (LinearMap.id - proj) = LinearMap.id - proj := by
    simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp, LinearMap.comp_id, h_idem]
    abel
  -- E = (I-P) ∘ E follows from (I-P) ∘ E = E
  have h_eq : (LinearMap.id - proj) ∘ₗ (complexifyDefect pi_dist hπ L P) =
              complexifyDefect pi_dist hπ L P := by
    calc (LinearMap.id - proj) ∘ₗ (complexifyDefect pi_dist hπ L P)
        = (LinearMap.id - proj) ∘ₗ ((LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj) := by rw [h_def]
      _ = ((LinearMap.id - proj) ∘ₗ (LinearMap.id - proj)) ∘ₗ L_c ∘ₗ proj := by
          simp only [LinearMap.comp_assoc]
      _ = (LinearMap.id - proj) ∘ₗ L_c ∘ₗ proj := by rw [h_complement_idem]
      _ = complexifyDefect pi_dist hπ L P := h_def.symm
  exact h_eq.symm

/-- **Lemma 6c**: E kills the complement, so Eψ = E(Pψ) for all ψ.

    **PROVEN**: Since E(I-P) = 0 (by `complexifyDefect_kills_complement`),
    for any ψ = Pψ + (I-P)ψ, we have Eψ = E(Pψ) + E((I-P)ψ) = E(Pψ) + 0. -/
theorem defect_factors_through_code (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (ψ : V → ℂ) :
    (complexifyDefect pi_dist hπ L P) ψ =
    (complexifyDefect pi_dist hπ L P) ((partitionToCodeSubspace pi_dist P).proj ψ) := by
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let E := complexifyDefect pi_dist hπ L P
  -- E kills complement: E ∘ (I - P) = 0
  have h_kills := complexifyDefect_kills_complement pi_dist hπ L P
  -- ψ = Pψ + (I-P)ψ, so Eψ = E(Pψ) + E((I-P)ψ) = E(Pψ) + 0
  have h_complement : E (ψ - proj ψ) = 0 := by
    have : (E ∘ₗ (LinearMap.id - proj)) ψ = E (ψ - proj ψ) := by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [← this, h_kills]
    simp
  calc E ψ = E (proj ψ + (ψ - proj ψ)) := by ring_nf
    _ = E (proj ψ) + E (ψ - proj ψ) := map_add E (proj ψ) (ψ - proj ψ)
    _ = E (proj ψ) + 0 := by rw [h_complement]
    _ = E (proj ψ) := add_zero _

/-- **Structural Property 6**: For partition codes with KL condition α = 0, ‖Eψ‖² = 0.

    **PROVEN for α = 0 case**:
    1. By `KL_gives_norm_sq_proportional`: ‖E(Pψ)‖² = α‖Pψ‖² for codewords
    2. By `defect_factors_through_code`: Eψ = E(Pψ)
    3. With α = 0: ‖Eψ‖² = ‖E(Pψ)‖² = 0·‖Pψ‖² = 0

    The remaining question is: why must α = 0? This is forced by the partition
    structure - different blocks have independent leakage patterns, making
    uniform α possible only when α = 0. -/
theorem KL_with_alpha_zero_implies_norm_sq_zero (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hKL : ∀ f, (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
        (0 : ℝ) • ((partitionToCodeSubspace pi_dist P).proj f)) :
    ∀ ψ, SGC.Axioms.GeometryGeneral.inner_pi pi_dist
      ((complexifyDefect pi_dist hπ L P) ψ) ((complexifyDefect pi_dist hπ L P) ψ) = 0 := by
  intro ψ
  let proj := (partitionToCodeSubspace pi_dist P).proj
  let E := complexifyDefect pi_dist hπ L P
  -- Eψ = E(Pψ) by defect_factors_through_code
  have h_factor := defect_factors_through_code pi_dist hπ L P ψ
  rw [h_factor]
  -- Pψ is a codeword: P(Pψ) = Pψ (by idempotence: P² = P)
  have h_idem := (partitionToCodeSubspace pi_dist P).idempotent
  have h_codeword : proj (proj ψ) = proj ψ := by
    -- h_idem : proj ∘ₗ proj = proj
    -- Apply both sides to ψ
    have h := LinearMap.congr_fun h_idem ψ
    simp only [LinearMap.comp_apply] at h
    exact h
  -- Apply KL_gives_norm_sq_proportional with α = 0
  have h_prop := KL_gives_norm_sq_proportional pi_dist hπ L P 0 hKL (proj ψ) h_codeword
  -- ‖E(Pψ)‖² = 0 · ‖Pψ‖² = 0
  simp only [Complex.ofReal_zero, zero_mul] at h_prop
  exact h_prop

/-- A constant real function is block-constant. -/
lemma const_isBlockConstant (P : Partition V) (c : ℝ) :
    IsBlockConstant P (fun _ => c) := fun _ _ _ => rfl

/-- **Sum Rule Infrastructure**: The all-ones vector is in the code subspace.

    **PROVEN**: The all-ones function 𝟙 is block-constant (constant on every block).
    By `partitionToCodeSubspace_proj_eq`, Π(𝟙) = CoarseProjector(Re 𝟙) + i·CoarseProjector(Im 𝟙).
    Since Re(𝟙) = 1 and Im(𝟙) = 0 are both constant (hence block-constant),
    and CoarseProjector fixes block-constant functions, we get Π(𝟙) = 1 + i·0 = 𝟙. -/
theorem all_ones_in_code (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (P : Partition V) :
    (partitionToCodeSubspace pi_dist P).proj (fun _ => (1 : ℂ)) = fun _ => 1 := by
  -- Use the characterization of the complex projector
  have h_proj_eq := partitionToCodeSubspace_proj_eq pi_dist hπ P (fun _ => (1 : ℂ))
  -- Re(1) = 1, Im(1) = 0
  have h_re : (fun w => RCLike.re ((fun _ : V => (1 : ℂ)) w)) = fun _ => (1 : ℝ) := by
    ext w; simp only [RCLike.one_re]
  have h_im : (fun w => RCLike.im ((fun _ : V => (1 : ℂ)) w)) = fun _ => (0 : ℝ) := by
    ext w; simp only [RCLike.one_im]
  -- Constant functions are block-constant
  have h_one_block : IsBlockConstant P (fun _ => (1 : ℝ)) := const_isBlockConstant P 1
  have h_zero_block : IsBlockConstant P (fun _ => (0 : ℝ)) := const_isBlockConstant P 0
  -- CoarseProjector fixes block-constant functions
  have h_fix_one : CoarseProjector P pi_dist hπ (fun _ => (1 : ℝ)) = fun _ => 1 :=
    CoarseProjector_fixes_block_constant P pi_dist hπ _ h_one_block
  have h_fix_zero : CoarseProjector P pi_dist hπ (fun _ => (0 : ℝ)) = fun _ => 0 :=
    CoarseProjector_fixes_block_constant P pi_dist hπ _ h_zero_block
  -- Combine
  rw [h_proj_eq, h_re, h_im, h_fix_one, h_fix_zero]
  ext v
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, add_zero]

/-- **Sum Rule Infrastructure**: The all-ones vector has positive norm squared.

    ‖𝟙‖² = Σᵥ π(v) > 0 since all π(v) > 0 and V is nonempty (Fintype). -/
axiom all_ones_norm_sq_pos (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    SGC.Axioms.GeometryGeneral.inner_pi pi_dist (fun _ : V => (1 : ℂ)) (fun _ => 1) ≠ 0

/-- Conservation: A matrix with row sums = 0 kills the all-ones vector.
    L_ℂ 𝟙 = 0 when ∀ v, Σ_w L(v,w) = 0. -/
lemma matrixToLinearMapComplex_kills_ones (L : Matrix V V ℝ) (hL_conserv : ∀ v, ∑ w, L v w = 0) :
    matrixToLinearMapComplex L (fun _ => 1) = 0 := by
  ext v
  simp only [matrixToLinearMapComplex, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_one]
  rw [← Complex.ofReal_sum]
  simp only [hL_conserv v, Complex.ofReal_zero]

/-- **Sum Rule Infrastructure**: Conservation implies E(𝟙) = 0.

    **PROVEN BY DEFINITION**: E = (I-P) L_c P, so
    E𝟙 = (I-P) L_c (P𝟙) = (I-P) L_c 𝟙  (since P𝟙 = 𝟙 by all_ones_in_code)
        = (I-P) 0 = 0                   (since L_c 𝟙 = 0 by conservation)

    This is the key conservation property that makes the Sum Rule work. -/
theorem defect_kills_all_ones (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hL_conserv : ∀ v, ∑ w, L v w = 0) :
    (complexifyDefect pi_dist hπ L P) (fun _ => 1) = 0 := by
  -- E = (I - proj) ∘ L_c ∘ proj by definition, applied to ones
  show ((LinearMap.id - (partitionToCodeSubspace pi_dist P).proj) ∘ₗ
        (matrixToLinearMapComplex L) ∘ₗ
        (partitionToCodeSubspace pi_dist P).proj) (fun _ => 1) = 0
  simp only [LinearMap.comp_apply]
  -- P𝟙 = 𝟙 (all-ones is in the code)
  rw [all_ones_in_code pi_dist hπ P]
  -- L_c 𝟙 = 0 (conservation)
  rw [matrixToLinearMapComplex_kills_ones L hL_conserv]
  -- (I-P) 0 = 0
  simp only [map_zero]

/-- **Sum Rule Infrastructure**: KL implies zero norm squared for all-ones.

    From defect_kills_all_ones: E𝟙 = 0, so ‖E𝟙‖² = 0.
    Combined with KL proportionality: 0 = α·‖𝟙‖².
    Since ‖𝟙‖² > 0, we get α = 0. -/
theorem partition_forces_alpha_zero (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (α : ℝ)
    (hL_conserv : ∀ v, ∑ w, L v w = 0)
    (hKL : ∀ f, (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
        (α : ℂ) • ((partitionToCodeSubspace pi_dist P).proj f)) :
    α = 0 := by
  -- The all-ones vector is a codeword
  let ones : V → ℂ := fun _ => 1
  have h_code : (partitionToCodeSubspace pi_dist P).proj ones = ones :=
    all_ones_in_code pi_dist hπ P
  -- E(𝟙) = 0 by conservation
  have h_E_ones : (complexifyDefect pi_dist hπ L P) ones = 0 :=
    defect_kills_all_ones pi_dist hπ L P hL_conserv
  -- ‖E(𝟙)‖² = 0
  have h_norm_zero : SGC.Axioms.GeometryGeneral.inner_pi pi_dist
      ((complexifyDefect pi_dist hπ L P) ones)
      ((complexifyDefect pi_dist hπ L P) ones) = 0 := by
    rw [h_E_ones]
    simp [SGC.Axioms.GeometryGeneral.inner_pi]
  -- By KL_gives_norm_sq_proportional: ‖E(𝟙)‖² = α·‖𝟙‖²
  have h_prop := KL_gives_norm_sq_proportional pi_dist hπ L P α hKL ones h_code
  -- So 0 = α·‖𝟙‖²
  rw [h_norm_zero] at h_prop
  -- ‖𝟙‖² = Σᵥ π(v) > 0 (since all π(v) > 0)
  have h_ones_pos : SGC.Axioms.GeometryGeneral.inner_pi pi_dist ones ones ≠ 0 :=
    all_ones_norm_sq_pos pi_dist hπ
  -- From 0 = α·‖𝟙‖² and ‖𝟙‖² ≠ 0, conclude α = 0
  have h_alpha_zero : (α : ℂ) = 0 := by
    by_contra h_ne
    have := mul_ne_zero h_ne h_ones_pos
    exact this (h_prop.symm)
  exact_mod_cast h_alpha_zero

/-- **Structural Property 6** (Corollary): KL condition forces ‖Eψ‖² = 0 for all ψ.

    **PROVEN** from `partition_forces_alpha_zero` and `KL_with_alpha_zero_implies_norm_sq_zero`. -/
theorem KL_implies_norm_sq_zero (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (α : ℝ)
    (hL_conserv : ∀ v, ∑ w, L v w = 0)
    (hKL : ∀ f, (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
        (α : ℂ) • ((partitionToCodeSubspace pi_dist P).proj f)) :
    ∀ ψ, SGC.Axioms.GeometryGeneral.inner_pi pi_dist
      ((complexifyDefect pi_dist hπ L P) ψ) ((complexifyDefect pi_dist hπ L P) ψ) = 0 := by
  -- First show α = 0
  have h_alpha_zero := partition_forces_alpha_zero pi_dist hπ L P α hL_conserv hKL
  -- Substitute into hKL
  rw [h_alpha_zero] at hKL
  -- Apply the α = 0 case theorem
  exact KL_with_alpha_zero_implies_norm_sq_zero pi_dist hπ L P hKL

/-- The main structural theorem: KL conditions force the defect to zero.

    **PROVEN** from `KL_implies_norm_sq_zero` and `operator_zero_iff_norm_sq_zero`.
    Note: We use real α (physically required for the leakage coefficient). -/
theorem knill_laflamme_forces_zero_defect (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hL_conserv : ∀ v, ∑ w, L v w = 0)
    (hKL : ∃ (α : ℝ), ∀ f,
      (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
      (α : ℂ) • ((partitionToCodeSubspace pi_dist P).proj f)) :
    complexifyDefect pi_dist hπ L P = 0 := by
  -- Extract α from KL condition
  obtain ⟨α, hα⟩ := hKL
  -- Use KL_implies_norm_sq_zero: KL implies ⟨Eψ, Eψ⟩ = 0 for all ψ
  have h_norm_zero := KL_implies_norm_sq_zero pi_dist hπ L P α hL_conserv hα
  -- Apply operator_zero_iff_norm_sq_zero
  exact (operator_zero_iff_norm_sq_zero pi_dist hπ _).mpr h_norm_zero

def defectToErrorOperators (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) : ErrorOperators V 1 :=
  { errors := fun _ => complexifyDefect pi_dist hπ L P }

/-- **Easy Direction**: If the defect operator is zero (exact lumpability),
    then Knill-Laflamme conditions hold trivially with α = 0.

    Proof idea: D = 0 ⟹ E = 0 ⟹ E†E = 0 ⟹ P E†E P = 0 = 0·P -/
theorem lumpability_implies_knill_laflamme (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hD : opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0) :
    let code := partitionToCodeSubspace pi_dist P
    let errors := defectToErrorOperators pi_dist hπ L P
    KnillLaflamme pi_dist code errors := by
  intro code errors
  -- When opNorm D = 0, the complexified defect E is also zero
  have hE_zero : complexifyDefect pi_dist hπ L P = 0 :=
    (complexifyDefect_zero_iff pi_dist hπ L P).mpr hD
  -- So E† E = 0, and P ∘ 0 ∘ P = 0 = 0 • P
  use fun _ _ => 0  -- α_ij = 0 for all i,j
  intro i j
  simp only [zero_smul]
  -- errors.errors _ = complexifyDefect = 0
  have hEi : errors.errors i = 0 := hE_zero
  have hEj : errors.errors j = 0 := hE_zero
  -- P ∘ 0† ∘ 0 ∘ P = 0
  rw [hEi, hEj, adjoint_pi_zero]
  simp only [LinearMap.comp_zero, LinearMap.zero_comp]

/-- **Hard Direction**: If Knill-Laflamme conditions hold,
    then the defect operator norm is zero.

    This is more subtle: KL says P E† E P ∝ P, which constrains the error structure.
    When the error comes from a classical defect operator, this forces D = 0.

    Note: Requires conservation (row sums = 0) for the Sum Rule proof. -/
theorem knill_laflamme_implies_lumpability (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hL_conserv : ∀ v, ∑ w, L v w = 0)
    (hKL : let code := partitionToCodeSubspace pi_dist P
           let errors := defectToErrorOperators pi_dist hπ L P
           KnillLaflamme pi_dist code errors) :
    opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0 := by
  -- Extract the KL condition: ∃ α, P E†E P = α P
  obtain ⟨α, hα⟩ := hKL
  -- For the single error case (n=1), the error is E = complexifyDefect
  -- hα says: code.proj ∘ E† ∘ E ∘ code.proj = α 0 0 • code.proj
  -- Rewrite to match knill_laflamme_forces_zero_defect hypothesis
  -- Note: α 0 0 is the scalar from the 1x1 matrix; for physical reasons it must be real
  -- We extract the real part as the physical leakage coefficient
  have hKL' : ∃ (α' : ℝ), ∀ f,
      (partitionToCodeSubspace pi_dist P).proj
        ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
          ((complexifyDefect pi_dist hπ L P)
            ((partitionToCodeSubspace pi_dist P).proj f))) =
      (α' : ℂ) • ((partitionToCodeSubspace pi_dist P).proj f) := by
    -- The KL coefficient must be real because ⟨E†E ψ, ψ⟩ = ‖Eψ‖² is real
    use (α 0 0).re  -- Extract real part
    intro f
    have h := hα 0 0
    simp only [defectToErrorOperators] at h
    have h_applied := congrFun (congrArg DFunLike.coe h) f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h_applied
    -- The KL condition gives α 0 0 • (P f) = P E† E P f
    -- For codeword ψ: ⟨α ψ, ψ⟩ = ⟨E† E ψ, ψ⟩ = ⟨Eψ, Eψ⟩ = ‖Eψ‖² (real!)
    -- So α must be real. We use inner_adjoint_self to establish this.
    -- Since ⟨E†E ψ, ψ⟩ = ‖Eψ‖² ∈ ℝ and ⟨α ψ, ψ⟩ = α ‖ψ‖², we get α ∈ ℝ.
    -- Formally: (α 0 0).im = 0, so α 0 0 = (α 0 0).re
    -- The imaginary part is zero by the real-valuedness of ‖Eψ‖²
    have h_real : (α 0 0).im = 0 := by
      -- E†E is self-adjoint: (E†E)† = E†E
      have h_sa : SGC.Axioms.GeometryGeneral.IsSelfAdjoint_pi pi_dist
          (adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P) ∘ₗ
           complexifyDefect pi_dist hπ L P) := by
        unfold SGC.Axioms.GeometryGeneral.IsSelfAdjoint_pi
        rw [SGC.Axioms.GeometryGeneral.adjoint_pi_comp]
        rw [SGC.Axioms.GeometryGeneral.adjoint_pi_involutive]
      -- Extract the KL condition in the right form
      have hKL_form : ∀ f, (partitionToCodeSubspace pi_dist P).proj
          ((adjoint_pi pi_dist (complexifyDefect pi_dist hπ L P))
            ((complexifyDefect pi_dist hπ L P)
              ((partitionToCodeSubspace pi_dist P).proj f))) =
          (α 0 0) • ((partitionToCodeSubspace pi_dist P).proj f) := by
        intro f
        have h := hα 0 0
        simp only [defectToErrorOperators] at h
        have h' := congrFun (congrArg DFunLike.coe h) f
        simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
        exact h'
      -- Apply KL_coefficient_real axiom
      exact KL_coefficient_real pi_dist hπ L P (α 0 0) h_sa hKL_form
    -- With α 0 0 real, we have (α 0 0).re = α 0 0
    have h_eq : ((α 0 0).re : ℂ) = α 0 0 := by
      rw [Complex.ext_iff]
      simp [h_real]
    rw [h_eq]
    exact h_applied
  -- Apply the key structural theorem
  have hE_zero := knill_laflamme_forces_zero_defect pi_dist hπ L P hL_conserv hKL'
  -- Convert E = 0 to opNorm D = 0
  exact (complexifyDefect_zero_iff pi_dist hπ L P).mp hE_zero

/-- The full bridge theorem combining both directions.

    Note: The hard direction (→) requires conservation (row sums = 0). -/
theorem knill_laflamme_iff_lumpability (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V)
    (hL_conserv : ∀ v, ∑ w, L v w = 0) :
    let code := partitionToCodeSubspace pi_dist P
    let errors := defectToErrorOperators pi_dist hπ L P
    (opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ) = 0) ↔
    KnillLaflamme pi_dist code errors :=
  ⟨lumpability_implies_knill_laflamme pi_dist hπ L P,
   knill_laflamme_implies_lumpability pi_dist hπ L P hL_conserv⟩

/-! ## Approximate Version: Error Bounds

For approximate lumpability, we get approximate QEC with error bounds. -/

/-- The defect norm in classical lumpability bounds the trace distance error
    in the quantum channel simulation. -/
axiom approximate_qec_bound (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (t : ℝ) (ht : 0 ≤ t) :
    let ε := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)
    let code := partitionToCodeSubspace pi_dist P
    ∀ (ρ : (V → ℂ) →ₗ[ℂ] (V → ℂ)) (hρ : IsDensityMatrix pi_dist ρ),
      traceDistance_pi pi_dist
        (code.proj ∘ₗ ρ ∘ₗ code.proj)
        ρ ≤ ε * t

/-! ## Quantum Validity Horizon

The validity horizon bounds how long coarse-grained dynamics remain accurate.
In the quantum setting, this becomes a bound on decoherence. -/

/-- The quantum validity horizon: time until trace distance exceeds threshold. -/
def quantumValidityHorizon (pi_dist : V → ℝ) (ℒ : Lindbladian V pi_dist)
    (code : CodeSubspace V pi_dist) (δ : ℝ) : ℝ :=
  sInf { t : ℝ | t > 0 ∧ ∀ (ρ : (V → ℂ) →ₗ[ℂ] (V → ℂ)) (hρ : IsDensityMatrix pi_dist ρ),
    traceDistance_pi pi_dist (code.proj ∘ₗ ρ ∘ₗ code.proj) ρ > δ }

/-- **Quantum Validity Horizon Theorem**:
    The validity horizon is bounded in terms of the spectral gap and code quality. -/
axiom quantum_validity_horizon_bound (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (δ : ℝ) (hδ : 0 < δ) :
    let ε := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)
    let code := partitionToCodeSubspace pi_dist P
    ε > 0 → ∃ (ℒ : Lindbladian V pi_dist),
      quantumValidityHorizon pi_dist ℒ code δ ≥ δ / ε

end Quantum
end Bridge
end SGC
