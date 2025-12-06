import FHDT.Core.Assumptions
import FHDT.Core.Projector
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open Matrix Real NormedSpace

namespace FHDT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {L H : Matrix V V ℝ} {pi_dist : V → ℝ}

/-- Heat semigroup K(t) = e^{tL}. -/
def HeatKernel (L : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  exp ℝ (t • L)

/-- At t = 0, the heat kernel is the identity matrix. -/
lemma HeatKernel_at_zero (L : Matrix V V ℝ) : HeatKernel L 0 = 1 := by
  simp [HeatKernel]

--------------------------------------------------------------------------------
-- HeatKernel ODE and Invariance Properties
--------------------------------------------------------------------------------

-- Use a specific matrix norm to help typeclass inference for exp derivative
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
/-- **Semigroup ODE**: The heat semigroup satisfies the matrix ODE u' = L *ᵥ u.
    For any initial vector g, the trajectory t ↦ HeatKernel L t *ᵥ g satisfies
    d/dt (HeatKernel L t *ᵥ g) = L *ᵥ (HeatKernel L t *ᵥ g).
    
    This is the fundamental calculus fact about matrix exponentials.
    
    **Proof idea:** Use hasDerivAt_exp_smul_const' from Mathlib, which says
    d/dt exp(t • A) = A * exp(t • A), then compose with the linear map mulVec g.
    The result follows from (L * exp(t•L)) *ᵥ g = L *ᵥ (exp(t•L) *ᵥ g) by associativity. -/
lemma heat_semigroup_deriv (L : Matrix V V ℝ) (g : V → ℝ) (t : ℝ) :
    deriv (fun s => HeatKernel L s *ᵥ g) t = L *ᵥ (HeatKernel L t *ᵥ g) := by
  -- Define the linear map (· *ᵥ g) : Matrix V V ℝ →ₗ[ℝ] (V → ℝ)
  let mulVec_g : Matrix V V ℝ →ₗ[ℝ] (V → ℝ) := 
    { toFun := fun M => M *ᵥ g
      map_add' := fun M N => Matrix.add_mulVec M N g
      map_smul' := fun c M => by ext v; simp [Matrix.smul_mulVec] }
  -- In finite dimension, linear maps are continuous
  let mulVec_clm : Matrix V V ℝ →L[ℝ] (V → ℝ) := 
    ⟨mulVec_g, LinearMap.continuous_of_finiteDimensional mulVec_g⟩
  -- HasDerivAt for the matrix exponential: d/dt exp(t•L) = L * exp(t•L)
  have h_exp : HasDerivAt (fun s : ℝ => exp ℝ (s • L)) (L * exp ℝ (t • L)) t := 
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t
  -- Compose with the continuous linear map using HasFDerivAt.comp_hasDerivAt
  -- A ContinuousLinearMap has its own fderivative
  have h_comp : HasDerivAt (fun s => mulVec_clm (exp ℝ (s • L))) (mulVec_clm (L * exp ℝ (t • L))) t := 
    mulVec_clm.hasFDerivAt.comp_hasDerivAt t h_exp
  -- Identify the composed function with our target
  have h_eq_fun : (fun s => mulVec_clm (exp ℝ (s • L))) = (fun s => HeatKernel L s *ᵥ g) := rfl
  -- Identify the derivative value: (L * exp(t•L)) *ᵥ g = L *ᵥ (exp(t•L) *ᵥ g)
  have h_val_eq : mulVec_clm (L * exp ℝ (t • L)) = L *ᵥ (HeatKernel L t *ᵥ g) := by
    simp only [mulVec_clm, mulVec_g, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
               HeatKernel]
    -- (L * exp(t•L)) *ᵥ g = L *ᵥ (exp(t•L) *ᵥ g) by associativity
    -- mulVec_mulVec says: M *ᵥ N *ᵥ v = (M * N) *ᵥ v, so we use .symm
    exact (Matrix.mulVec_mulVec g L (exp ℝ (t • L))).symm
  rw [h_eq_fun, h_val_eq] at h_comp
  exact h_comp.deriv

-- Reuse the local instance for coordinate differentiability
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
/-- Coordinatewise differentiability of HeatKernel trajectory.
    Each coordinate t ↦ (HeatKernel L t *ᵥ g) v is differentiable.
    This follows from the smoothness of the matrix exponential. -/
lemma HeatKernel_coord_differentiable (L : Matrix V V ℝ) (g : V → ℝ) (v : V) (t : ℝ) :
    DifferentiableAt ℝ (fun s => (HeatKernel L s *ᵥ g) v) t := by
  -- First, establish HasDerivAt for the vector-valued function (same as heat_semigroup_deriv)
  let mulVec_g : Matrix V V ℝ →ₗ[ℝ] (V → ℝ) := 
    { toFun := fun M => M *ᵥ g
      map_add' := fun M N => Matrix.add_mulVec M N g
      map_smul' := fun c M => by ext w; simp [Matrix.smul_mulVec] }
  let mulVec_clm : Matrix V V ℝ →L[ℝ] (V → ℝ) := 
    ⟨mulVec_g, LinearMap.continuous_of_finiteDimensional mulVec_g⟩
  have h_exp : HasDerivAt (fun s : ℝ => exp ℝ (s • L)) (L * exp ℝ (t • L)) t := 
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t
  have h_vec : HasDerivAt (fun s => mulVec_clm (exp ℝ (s • L))) (mulVec_clm (L * exp ℝ (t • L))) t := 
    mulVec_clm.hasFDerivAt.comp_hasDerivAt t h_exp
  -- Now compose with evaluation at v: ev_v : (V → ℝ) →L[ℝ] ℝ
  let ev_v : (V → ℝ) →L[ℝ] ℝ := 
    { toFun := fun f => f v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := continuous_apply v }
  have h_coord : HasDerivAt (fun s => ev_v (mulVec_clm (exp ℝ (s • L)))) 
                            (ev_v (mulVec_clm (L * exp ℝ (t • L)))) t := 
    ev_v.hasFDerivAt.comp_hasDerivAt t h_vec
  -- The composed function is exactly (fun s => (HeatKernel L s *ᵥ g) v)
  have h_eq : (fun s => ev_v (mulVec_clm (exp ℝ (s • L)))) = (fun s => (HeatKernel L s *ᵥ g) v) := rfl
  rw [h_eq] at h_coord
  exact h_coord.differentiableAt

/-- Grönwall uniqueness: a nonnegative function that starts at zero and satisfies
    a linear differential inequality must be identically zero. 
    
    **Key insight**: Consider φ(s) = ψ(s) * exp(-C*s). Then:
    - φ'(s) = (ψ'(s) - C*ψ(s)) * exp(-C*s) ≤ 0  (from ψ' ≤ C*ψ)
    - φ(0) = 0, φ ≥ 0, φ' ≤ 0 ⟹ φ ≡ 0 on [0, ∞)
    
    For s ≤ 0, use the lower bound -C*ψ ≤ ψ' on a reflected function. -/
lemma gronwall_zero_of_abs_deriv_le {ψ : ℝ → ℝ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hψ_diff : Differentiable ℝ ψ)
    (hψ_nonneg : ∀ s, 0 ≤ ψ s)
    (hψ0 : ψ 0 = 0)
    (hψ_ineq : ∀ s, |deriv ψ s| ≤ C * ψ s) :
    ∀ s, ψ s = 0 := by
  -- The bound |ψ'| ≤ C*ψ gives both directions
  have hψ_upper : ∀ s, deriv ψ s ≤ C * ψ s := fun s => by
    have := hψ_ineq s
    rw [abs_le] at this
    linarith [this.2]
  have hψ_lower : ∀ s, -(C * ψ s) ≤ deriv ψ s := fun s => by
    have := hψ_ineq s
    rw [abs_le] at this
    exact this.1
  -- 
  -- Case 1: s ≥ 0
  -- Use auxiliary φ(s) = ψ(s) * exp(-C*s), show φ' ≤ 0, φ(0) = 0, φ ≥ 0 ⟹ φ ≡ 0
  have h_nonneg_case : ∀ s ≥ 0, ψ s = 0 := by
    intro s hs
    -- Define φ(r) = ψ(r) * exp(-C*r)
    let φ : ℝ → ℝ := fun r => ψ r * Real.exp (-C * r)
    -- φ is differentiable
    have hφ_diff : Differentiable ℝ φ := by
      intro r
      exact (hψ_diff r).mul (((differentiable_const (-C)).mul differentiable_id).exp.differentiableAt)
    -- φ(0) = 0
    have hφ0 : φ 0 = 0 := by simp [φ, hψ0]
    -- φ' = (ψ' - C*ψ) * exp(-C*r)
    have hφ_deriv : ∀ r, deriv φ r = (deriv ψ r - C * ψ r) * Real.exp (-C * r) := by
      intro r
      have h1 : HasDerivAt ψ (deriv ψ r) r := (hψ_diff r).hasDerivAt
      have h2 : HasDerivAt (fun x => Real.exp (-C * x)) (-C * Real.exp (-C * r)) r := by
        have := ((hasDerivAt_id r).const_mul (-C)).exp
        simp only [mul_one, id_eq] at this
        convert this using 1; ring
      have h_prod := h1.mul h2
      have h_eq : deriv ψ r * Real.exp (-C * r) + ψ r * (-C * Real.exp (-C * r)) = 
                  (deriv ψ r - C * ψ r) * Real.exp (-C * r) := by ring
      calc deriv φ r = deriv ψ r * Real.exp (-C * r) + ψ r * (-C * Real.exp (-C * r)) := h_prod.deriv
        _ = (deriv ψ r - C * ψ r) * Real.exp (-C * r) := h_eq
    -- φ' ≤ 0 (since ψ' - C*ψ ≤ 0 and exp > 0)
    have hφ_deriv_nonpos : ∀ r, deriv φ r ≤ 0 := by
      intro r
      rw [hφ_deriv]
      have h_diff_nonpos : deriv ψ r - C * ψ r ≤ 0 := by linarith [hψ_upper r]
      exact mul_nonpos_of_nonpos_of_nonneg h_diff_nonpos (Real.exp_nonneg _)
    -- φ ≥ 0 (since ψ ≥ 0 and exp > 0)
    have hφ_nonneg : ∀ r, 0 ≤ φ r := fun r => mul_nonneg (hψ_nonneg r) (Real.exp_nonneg _)
    -- By Monotone argument: φ' ≤ 0 means φ is nonincreasing
    -- φ(0) = 0 and φ ≥ 0, φ nonincreasing ⟹ φ(s) ≤ 0 for s ≥ 0
    -- Combined with φ(s) ≥ 0, we get φ(s) = 0
    have hφs_le : φ s ≤ 0 := by
      by_cases hs_eq : s = 0
      · simp [hs_eq, hφ0]
      · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_eq)
        -- Use that φ is antitone on [0, s] since φ' ≤ 0
        have hφ_antitone : AntitoneOn φ (Set.Icc 0 s) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s) (hφ_diff.continuous.continuousOn)
          · exact hφ_diff.differentiableOn.mono interior_subset
          · intro x hx; exact hφ_deriv_nonpos x
        have h0_mem : (0 : ℝ) ∈ Set.Icc 0 s := Set.left_mem_Icc.mpr hs
        have hs_mem : s ∈ Set.Icc 0 s := Set.right_mem_Icc.mpr hs
        have := hφ_antitone h0_mem hs_mem hs
        simp only [hφ0] at this
        exact this
    have hφs_eq : φ s = 0 := le_antisymm hφs_le (hφ_nonneg s)
    -- φ(s) = ψ(s) * exp(-C*s) = 0 and exp(-C*s) ≠ 0, so ψ(s) = 0
    simp only [φ] at hφs_eq
    have h_exp_ne : Real.exp (-C * s) ≠ 0 := Real.exp_ne_zero _
    exact (mul_eq_zero.mp hφs_eq).resolve_right h_exp_ne
  -- 
  -- Case 2: s < 0
  -- Consider θ(r) = ψ(-r) for r ≥ 0, apply same argument
  have h_neg_case : ∀ s ≤ 0, ψ s = 0 := by
    intro s hs
    let θ : ℝ → ℝ := fun r => ψ (-r)
    have hθ_at_neg_s : θ (-s) = ψ s := by simp [θ]
    have h_neg_s_nonneg : 0 ≤ -s := by linarith
    have hθ_diff : Differentiable ℝ θ := hψ_diff.comp differentiable_neg
    have hθ0 : θ 0 = 0 := by simp [θ, hψ0]
    have hθ_nonneg : ∀ r, 0 ≤ θ r := fun r => hψ_nonneg (-r)
    have hθ_upper : ∀ r, deriv θ r ≤ C * θ r := by
      intro r
      have h_chain : deriv θ r = -deriv ψ (-r) := by
        have := (hψ_diff (-r)).hasDerivAt.comp r (hasDerivAt_neg r)
        simp only [Function.comp_def] at this
        have h_eq : deriv θ r = deriv ψ (-r) * -1 := this.deriv
        linarith
      rw [h_chain]
      have h_lower := hψ_lower (-r)
      linarith
    -- Apply the same φ argument to θ
    let φθ : ℝ → ℝ := fun r => θ r * Real.exp (-C * r)
    have hφθ_diff : Differentiable ℝ φθ := by
      intro r
      exact (hθ_diff r).mul (((differentiable_const (-C)).mul differentiable_id).exp.differentiableAt)
    have hφθ0 : φθ 0 = 0 := by simp [φθ, hθ0]
    have hφθ_deriv_nonpos : ∀ r, deriv φθ r ≤ 0 := by
      intro r
      have h1 : HasDerivAt θ (deriv θ r) r := (hθ_diff r).hasDerivAt
      have h2 : HasDerivAt (fun x => Real.exp (-C * x)) (-C * Real.exp (-C * r)) r := by
        have := ((hasDerivAt_id r).const_mul (-C)).exp
        simp only [mul_one, id_eq] at this
        convert this using 1; ring
      have h_prod := h1.mul h2
      have h_deriv_eq : deriv φθ r = (deriv θ r - C * θ r) * Real.exp (-C * r) := by
        have h_eq : deriv θ r * Real.exp (-C * r) + θ r * (-C * Real.exp (-C * r)) = 
                    (deriv θ r - C * θ r) * Real.exp (-C * r) := by ring
        calc deriv φθ r = deriv θ r * Real.exp (-C * r) + θ r * (-C * Real.exp (-C * r)) := h_prod.deriv
          _ = (deriv θ r - C * θ r) * Real.exp (-C * r) := h_eq
      rw [h_deriv_eq]
      have h_diff_nonpos : deriv θ r - C * θ r ≤ 0 := by linarith [hθ_upper r]
      exact mul_nonpos_of_nonpos_of_nonneg h_diff_nonpos (Real.exp_nonneg _)
    have hφθ_nonneg : ∀ r, 0 ≤ φθ r := fun r => mul_nonneg (hθ_nonneg r) (Real.exp_nonneg _)
    have hφθ_neg_s_le : φθ (-s) ≤ 0 := by
      by_cases hs_eq : -s = 0
      · simp [hs_eq, hφθ0]
      · have hs_pos : 0 < -s := lt_of_le_of_ne h_neg_s_nonneg (Ne.symm hs_eq)
        have hφθ_antitone : AntitoneOn φθ (Set.Icc 0 (-s)) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (-s)) (hφθ_diff.continuous.continuousOn)
          · exact hφθ_diff.differentiableOn.mono interior_subset
          · intro x _; exact hφθ_deriv_nonpos x
        have h0_mem : (0 : ℝ) ∈ Set.Icc 0 (-s) := Set.left_mem_Icc.mpr h_neg_s_nonneg
        have hs_mem : (-s) ∈ Set.Icc 0 (-s) := Set.right_mem_Icc.mpr h_neg_s_nonneg
        have := hφθ_antitone h0_mem hs_mem h_neg_s_nonneg
        simp only [hφθ0] at this
        exact this
    have hφθ_neg_s_eq : φθ (-s) = 0 := le_antisymm hφθ_neg_s_le (hφθ_nonneg (-s))
    simp only [φθ] at hφθ_neg_s_eq
    have h_exp_ne : Real.exp (-C * (-s)) ≠ 0 := Real.exp_ne_zero _
    have hθ_neg_s_eq : θ (-s) = 0 := (mul_eq_zero.mp hφθ_neg_s_eq).resolve_right h_exp_ne
    rw [← hθ_at_neg_s]
    exact hθ_neg_s_eq
  -- 
  -- Combine both cases
  intro s
  by_cases hs : s ≥ 0
  · exact h_nonneg_case s hs
  · push_neg at hs; exact h_neg_case s (le_of_lt hs)

/-- **Stationarity**: The heat semigroup preserves constant vectors.
    
    **ODE Proof**: Let u(t) = HeatKernel L t *ᵥ 1 and w(t) = u(t) - 1.
    - w(0) = u(0) - 1 = 1 - 1 = 0
    - w'(t) = u'(t) = L *ᵥ u(t) = L *ᵥ (w(t) + 1) = L *ᵥ w(t)  (since L *ᵥ 1 = 0)
    - So w solves the homogeneous ODE w' = L *ᵥ w with w(0) = 0
    - Consider ψ(t) = ‖w(t)‖². Then ψ(0) = 0 and ψ' = 2⟨w', w⟩ = 2⟨Lw, w⟩
    - By Grönwall-type argument, ψ ≡ 0, hence w ≡ 0, hence u ≡ 1. -/
lemma HeatKernel_preserves_one (L : Matrix V V ℝ) 
    (hL1 : L *ᵥ constant_vec_one = 0) (t : ℝ) :
    HeatKernel L t *ᵥ constant_vec_one = constant_vec_one := by
  -- Define u(t) := HeatKernel L t *ᵥ 1
  let u : ℝ → (V → ℝ) := fun s => HeatKernel L s *ᵥ constant_vec_one
  -- 
  -- Initial condition: u(0) = 1
  have hu0 : u 0 = constant_vec_one := by
    show HeatKernel L 0 *ᵥ constant_vec_one = constant_vec_one
    have h1 : HeatKernel L 0 = 1 := by simp [HeatKernel]
    rw [h1, one_mulVec]
  -- 
  -- ODE for u: u'(t) = L *ᵥ u(t) by heat_semigroup_deriv
  have hu' : ∀ s, deriv u s = L *ᵥ u s := by
    intro s
    exact heat_semigroup_deriv L constant_vec_one s
  -- 
  -- Define w(t) := u(t) - 1
  let w : ℝ → (V → ℝ) := fun s => u s - constant_vec_one
  -- 
  -- w(0) = 0
  have hw0 : w 0 = 0 := by
    simp only [w, hu0, sub_self]
  -- 
  -- w'(t) = L *ᵥ w(t) follows from:
  -- - deriv w = deriv u (since w = u - const)
  -- - deriv u = L *ᵥ u (by hu')
  -- - L *ᵥ u = L *ᵥ (w + 1) = L *ᵥ w (since L *ᵥ 1 = 0)
  -- 
  -- ════════════════════════════════════════════════════════════════════════════
  -- Grönwall-style ODE uniqueness: w(0) = 0, w' = L *ᵥ w ⟹ w ≡ 0
  -- ════════════════════════════════════════════════════════════════════════════
  -- 
  -- Define energy ψ(t) = ∑ v, w(t,v)² (Euclidean norm squared)
  let ψ : ℝ → ℝ := fun s => ∑ v : V, (w s v) ^ 2
  -- 
  -- ψ(0) = 0
  have hψ0 : ψ 0 = 0 := by
    simp only [ψ, hw0, Pi.zero_apply, sq, mul_zero, Finset.sum_const_zero]
  -- 
  -- ψ ≥ 0 always
  have hψ_nonneg : ∀ s, 0 ≤ ψ s := by
    intro s
    apply Finset.sum_nonneg
    intro v _
    exact sq_nonneg (w s v)
  -- 
  -- ψ is differentiable (finite sum of differentiable squares)
  have hψ_diff : Differentiable ℝ ψ := by
    -- Define the family F v = fun s => (w s v)²
    let F : V → (ℝ → ℝ) := fun v => fun s => (w s v) ^ 2
    have hψ_eq : ψ = ∑ v : V, F v := by ext s; simp [ψ, F, Finset.sum_apply]
    rw [hψ_eq]
    apply Differentiable.sum
    intro v _
    -- F v is differentiable as composition of w_v (differentiable) and x²
    apply Differentiable.pow
    -- w s v = u s v - 1
    intro s
    have := HeatKernel_coord_differentiable L constant_vec_one v s
    simp only [w, u, Pi.sub_apply] at *
    exact DifferentiableAt.sub this (differentiableAt_const _)
  -- 
  -- ════════════════════════════════════════════════════════════════════════════
  -- Grönwall uniqueness: apply the helper lemma with a crude but sufficient bound
  -- ════════════════════════════════════════════════════════════════════════════
  -- 
  -- The key bound: |ψ'| ≤ C * ψ for some constant C depending on L
  -- This follows from the energy derivative formula and Cauchy-Schwarz
  -- For now, use a simple constant that suffices
  let C : ℝ := 2 * (Finset.univ (α := V)).card * ((∑ i : V, ∑ j : V, (L i j)^2) + 1)
  have hC_nonneg : 0 ≤ C := by
    apply mul_nonneg
    apply mul_nonneg
    · linarith
    · exact Nat.cast_nonneg _
    · have h_sum : 0 ≤ ∑ i : V, ∑ j : V, (L i j)^2 := by
        apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; exact sq_nonneg _
      linarith
  -- 
  -- The energy bound |ψ'(s)| ≤ C * ψ(s) holds because:
  -- ψ'(s) = 2⟨w(s), L *ᵥ w(s)⟩ (Euclidean inner product)
  -- |⟨w, Lw⟩| ≤ ‖w‖ · ‖Lw‖ ≤ ‖L‖_op · ‖w‖² (by Cauchy-Schwarz and operator norm bound)
  -- In finite dimension, ‖L‖_op is bounded by a constant depending on L's entries
  -- 
  have hψ_ineq : ∀ s, |deriv ψ s| ≤ C * ψ s := by
    intro s
    -- ══════════════════════════════════════════════════════════════════════════
    -- Strategy: Use deriv_sum to compute ψ' explicitly, then apply CS bounds
    -- ══════════════════════════════════════════════════════════════════════════
    -- 
    -- Frobenius norm squared of L
    let L_frob := ∑ i : V, ∑ j : V, (L i j)^2
    have hL_frob_nonneg : 0 ≤ L_frob := 
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    -- 
    -- Cauchy-Schwarz for finite sums: (∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)
    have cs_finite : ∀ (a b : V → ℝ), (∑ v, a v * b v)^2 ≤ (∑ v, (a v)^2) * (∑ v, (b v)^2) := by
      intro a b
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    -- 
    -- Each coordinate of w is differentiable
    have hw_coord_diff : ∀ v, Differentiable ℝ (fun r => w r v) := by
      intro v r
      have := HeatKernel_coord_differentiable L constant_vec_one v r
      simp only [w, u, Pi.sub_apply] at *
      exact DifferentiableAt.sub this (differentiableAt_const _)
    -- 
    -- Derivative of each coordinate: (w r v)' = (L *ᵥ w r) v
    have hw_coord_deriv : ∀ v r, deriv (fun t => w t v) r = (L *ᵥ w r) v := by
      intro v r
      -- w r = u r - 1, so deriv w = deriv u - deriv 1 = deriv u
      have h_u_diff : DifferentiableAt ℝ (fun t => u t v) r := 
        HeatKernel_coord_differentiable L constant_vec_one v r
      have h1_diff : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) r := differentiableAt_const _
      have h_deriv_w : deriv (fun t => w t v) r = deriv (fun t => u t v) r - deriv (fun _ => (1 : ℝ)) r := by
        have heq : (fun t => w t v) = (fun t => u t v) - (fun _ => (1 : ℝ)) := by
          ext t; simp only [w, u, Pi.sub_apply, constant_vec_one]
        rw [heq, deriv_sub h_u_diff h1_diff]
      rw [h_deriv_w, deriv_const, sub_zero]
      -- deriv (fun t => u t v) r = (deriv u r) v
      have h_all_diff : ∀ x : V, DifferentiableAt ℝ (fun t => u t x) r := 
        fun x => HeatKernel_coord_differentiable L constant_vec_one x r
      have h_deriv_pi := deriv_pi h_all_diff
      rw [← congr_fun h_deriv_pi v]
      rw [hu' r]
      -- L *ᵥ u r = L *ᵥ (w r + 1) = L *ᵥ w r (since L *ᵥ 1 = 0)
      have h_u_eq : u r = w r + constant_vec_one := by ext x; simp only [w, Pi.sub_apply, sub_add_cancel]
      rw [h_u_eq, Matrix.mulVec_add, hL1, add_zero]
    -- 
    -- The derivative of ψ using deriv_sum
    have hψ_deriv_formula : deriv ψ s = 2 * ∑ v, w s v * (L *ᵥ w s) v := by
      -- ψ = ∑ v, F v where F v = fun r => (w r v)²
      let F : V → (ℝ → ℝ) := fun v => fun r => (w r v)^2
      have hψ_eq : ψ = ∑ v : V, F v := by ext r; simp only [ψ, F, Finset.sum_apply]
      rw [hψ_eq]
      -- Use deriv_sum (each F v is differentiable)
      have hF_diff : ∀ v, Differentiable ℝ (F v) := fun v => (hw_coord_diff v).pow 2
      rw [deriv_sum (fun v _ => (hF_diff v).differentiableAt)]
      -- Compute deriv (F v) s = 2 * w s v * (L *ᵥ w s) v
      have h_deriv_F : ∀ v, deriv (F v) s = 2 * w s v * (L *ᵥ w s) v := by
        intro v
        have h_has : HasDerivAt (fun r => w r v) (deriv (fun r => w r v) s) s := 
          (hw_coord_diff v s).hasDerivAt
        have h_sq := h_has.pow 2
        simp only [Nat.add_one_sub_one, pow_one] at h_sq
        -- deriv (F v) s = deriv (fun r => (w r v)^2) s
        -- h_sq gives HasDerivAt ((fun r => w r v)^2) (2 * w s v * deriv ...) s
        -- We need to show this equals deriv (F v) s
        have h_eq : deriv (F v) s = 2 * w s v * deriv (fun r => w r v) s := h_sq.deriv
        rw [h_eq, hw_coord_deriv v s]
      simp_rw [h_deriv_F]
      -- ∑ v, 2 * w s v * (L *ᵥ w s) v = 2 * ∑ v, w s v * (L *ᵥ w s) v
      rw [Finset.sum_congr rfl (fun v _ => by ring : ∀ v ∈ Finset.univ, 
          2 * w s v * (L *ᵥ w s) v = 2 * (w s v * (L *ᵥ w s) v))]
      rw [← Finset.mul_sum]
    -- 
    -- Bound ∑ v (Lw)_v² ≤ L_frob * ψ s
    have h_Lw_bound : ∑ v : V, ((L *ᵥ w s) v)^2 ≤ L_frob * ψ s := by
      have h_each : ∀ v : V, ((L *ᵥ w s) v)^2 ≤ (∑ j : V, (L v j)^2) * ψ s := by
        intro v
        simp only [mulVec, dotProduct]
        calc (∑ j : V, L v j * w s j)^2 ≤ (∑ j : V, (L v j)^2) * (∑ j : V, (w s j)^2) := cs_finite (L v) (w s)
          _ = (∑ j : V, (L v j)^2) * ψ s := rfl
      calc ∑ v : V, ((L *ᵥ w s) v)^2 
          ≤ ∑ v : V, (∑ j : V, (L v j)^2) * ψ s := Finset.sum_le_sum (fun v _ => h_each v)
        _ = (∑ v : V, ∑ j : V, (L v j)^2) * ψ s := by rw [Finset.sum_mul]
        _ = L_frob * ψ s := rfl
    -- 
    -- Key energy bound: |⟨w, Lw⟩| ≤ sqrt(L_frob) * ψ s
    have h_inner_bound : |∑ v : V, w s v * (L *ᵥ w s) v| ≤ Real.sqrt L_frob * ψ s := by
      have h_cs := cs_finite (w s) (L *ᵥ w s)
      have h_sq_le : (∑ v, w s v * (L *ᵥ w s) v)^2 ≤ (ψ s) * (∑ v, ((L *ᵥ w s) v)^2) := h_cs
      have h_rhs_le : (ψ s) * (∑ v, ((L *ᵥ w s) v)^2) ≤ (ψ s) * (L_frob * ψ s) := 
        mul_le_mul_of_nonneg_left h_Lw_bound (hψ_nonneg s)
      have h_sq_final : (∑ v, w s v * (L *ᵥ w s) v)^2 ≤ L_frob * (ψ s)^2 := by
        calc (∑ v, w s v * (L *ᵥ w s) v)^2 ≤ (ψ s) * (L_frob * ψ s) := le_trans h_sq_le h_rhs_le
          _ = L_frob * (ψ s)^2 := by ring
      calc |∑ v : V, w s v * (L *ᵥ w s) v| 
          = Real.sqrt ((∑ v, w s v * (L *ᵥ w s) v)^2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (L_frob * (ψ s)^2) := Real.sqrt_le_sqrt h_sq_final
        _ = Real.sqrt L_frob * Real.sqrt ((ψ s)^2) := Real.sqrt_mul hL_frob_nonneg _
        _ = Real.sqrt L_frob * |ψ s| := by rw [Real.sqrt_sq_eq_abs]
        _ = Real.sqrt L_frob * ψ s := by rw [abs_of_nonneg (hψ_nonneg s)]
    -- 
    -- |ψ'(s)| = |2 * ∑ w * Lw| ≤ 2 * sqrt(L_frob) * ψ s
    have h_deriv_bound : |deriv ψ s| ≤ 2 * Real.sqrt L_frob * ψ s := by
      rw [hψ_deriv_formula]
      rw [abs_mul]
      simp only [abs_of_pos (by linarith : (0 : ℝ) < 2)]
      calc 2 * |∑ v : V, w s v * (L *ᵥ w s) v| 
          ≤ 2 * (Real.sqrt L_frob * ψ s) := by apply mul_le_mul_of_nonneg_left h_inner_bound; linarith
        _ = 2 * Real.sqrt L_frob * ψ s := by ring
    -- 
    -- sqrt(x) ≤ x + 1 for all x ≥ 0
    have h_sqrt_le : Real.sqrt L_frob ≤ L_frob + 1 := by
      by_cases h : L_frob ≤ 1
      · calc Real.sqrt L_frob ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
          _ = 1 := Real.sqrt_one
          _ ≤ L_frob + 1 := by linarith [hL_frob_nonneg]
      · push_neg at h
        have h_ge_one : 1 ≤ L_frob := le_of_lt h
        calc Real.sqrt L_frob ≤ L_frob := by
              rw [Real.sqrt_le_iff]; constructor
              · exact hL_frob_nonneg
              · calc L_frob = L_frob * 1 := (mul_one _).symm
                  _ ≤ L_frob * L_frob := mul_le_mul_of_nonneg_left h_ge_one hL_frob_nonneg
                  _ = L_frob ^ 2 := (sq _).symm
          _ ≤ L_frob + 1 := by linarith
    -- 
    -- 2 * sqrt(L_frob) ≤ C
    -- Note: C = 2 * |V| * (L_frob + 1), so we need 2 * sqrt(L_frob) ≤ 2 * |V| * (L_frob + 1)
    -- Case split on whether V is empty
    have h_C_ge : 2 * Real.sqrt L_frob ≤ C := by
      by_cases hV : (Finset.univ (α := V)).card = 0
      · -- If V is empty, then L_frob = 0 (empty sum), so sqrt(L_frob) = 0
        have h_L_frob_zero : L_frob = 0 := by
          have h_univ_empty : (Finset.univ : Finset V) = ∅ := Finset.card_eq_zero.mp hV
          calc L_frob = ∑ i : V, ∑ j : V, (L i j)^2 := rfl
            _ = ∑ i ∈ (∅ : Finset V), ∑ j : V, (L i j)^2 := by rw [← h_univ_empty]
            _ = 0 := Finset.sum_empty
        have hC_zero : C = 0 := by 
          calc C = 2 * (Finset.univ (α := V)).card * ((∑ i : V, ∑ j : V, (L i j)^2) + 1) := rfl
            _ = 2 * 0 * ((∑ i : V, ∑ j : V, (L i j)^2) + 1) := by rw [hV]; simp
            _ = 0 := by ring
        rw [h_L_frob_zero, hC_zero, Real.sqrt_zero, mul_zero]
      · -- V is nonempty, so |V| ≥ 1
        have h_card_pos : 1 ≤ (Finset.univ (α := V)).card := Nat.one_le_iff_ne_zero.mpr hV
        calc 2 * Real.sqrt L_frob 
            ≤ 2 * (L_frob + 1) := mul_le_mul_of_nonneg_left h_sqrt_le (by linarith)
          _ = 2 * 1 * (L_frob + 1) := by ring
          _ ≤ 2 * (Finset.univ (α := V)).card * (L_frob + 1) := by
              apply mul_le_mul_of_nonneg_right _ (by linarith [hL_frob_nonneg])
              apply mul_le_mul_of_nonneg_left (Nat.one_le_cast.mpr h_card_pos) (by linarith)
          _ = C := rfl
    -- Final bound
    calc |deriv ψ s| ≤ 2 * Real.sqrt L_frob * ψ s := h_deriv_bound
      _ ≤ C * ψ s := mul_le_mul_of_nonneg_right h_C_ge (hψ_nonneg s)
  -- 
  -- Apply Grönwall uniqueness lemma
  have hψ_zero : ∀ s, ψ s = 0 := gronwall_zero_of_abs_deriv_le hC_nonneg hψ_diff hψ_nonneg hψ0 hψ_ineq
  -- 
  -- From ψ(t) = 0 conclude w(t) = 0
  have hw_zero : w t = 0 := by
    have hψt := hψ_zero t
    ext v
    have h_sum_zero : ∑ v' : V, (w t v') ^ 2 = 0 := hψt
    have h_each_nonneg : ∀ v' : V, 0 ≤ (w t v') ^ 2 := fun v' => sq_nonneg _
    have h_in_sum : v ∈ Finset.univ := Finset.mem_univ v
    have h_term_zero := Finset.sum_eq_zero_iff_of_nonneg (fun v' _ => h_each_nonneg v') |>.mp h_sum_zero v h_in_sum
    exact sq_eq_zero_iff.mp h_term_zero
  -- 
  -- Conclude: u t = w t + 1 = 0 + 1 = 1
  simp only [w] at hw_zero
  exact sub_eq_zero.mp hw_zero

/-- **L maps into 1⊥**: A consequence of the sector relation and stationarity.
    From the sector relation ⟨Lu,v⟩_π + ⟨u,Lv⟩_π = -2⟨Hu,v⟩_π with v=1 and L*1=H*1=0,
    we get ⟨Lu, 1⟩_π = 0 for all u. -/
lemma L_maps_into_one_orth {pi_dist : V → ℝ}
    (L H : Matrix V V ℝ) 
    (hL1 : L *ᵥ constant_vec_one = 0)
    (h_H_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (hH1 : H *ᵥ constant_vec_one = 0)
    (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) = 
                    -2 * inner_pi pi_dist (H *ᵥ u) v)
    (u : V → ℝ) :
    inner_pi pi_dist (L *ᵥ u) constant_vec_one = 0 := by
  -- From h_rel with v = 1: ⟨Lu, 1⟩ + ⟨u, L*1⟩ = -2⟨Hu, 1⟩
  -- With L*1 = 0: ⟨Lu, 1⟩ = -2⟨Hu, 1⟩
  -- By self-adjointness of H and H*1 = 0: ⟨Hu, 1⟩ = ⟨u, H*1⟩ = 0
  have h := h_rel u constant_vec_one
  simp only [hL1, inner_pi_zero_right, add_zero] at h
  -- h : ⟨Lu, 1⟩ = -2⟨Hu, 1⟩
  have h_Hu_1 : inner_pi pi_dist (H *ᵥ u) constant_vec_one = 0 := by
    rw [h_H_sa u constant_vec_one, hH1, inner_pi_zero_right]
  linarith

/-- **Invariance of 1⊥**: The heat semigroup maps vectors orthogonal to 1 
    to vectors orthogonal to 1 (in the π-weighted inner product).
    
    **ODE Proof**: Define φ(t) := ⟨HeatKernel L t *ᵥ g, 1⟩_π.
    - φ(0) = ⟨g, 1⟩_π = 0 by hypothesis hg
    - φ'(t) = ⟨d/dt (HeatKernel L t *ᵥ g), 1⟩_π 
            = ⟨L *ᵥ (HeatKernel L t *ᵥ g), 1⟩_π  by heat_semigroup_deriv
            = 0  by L_maps_into_one_orth
    - Since φ' = 0 and φ(0) = 0, we have φ ≡ 0. -/
lemma HeatKernel_maps_one_orth_to_one_orth {pi_dist : V → ℝ}
    (L H : Matrix V V ℝ)
    (hL1 : L *ᵥ constant_vec_one = 0)
    (h_H_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (hH1 : H *ᵥ constant_vec_one = 0)
    (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) = 
                    -2 * inner_pi pi_dist (H *ᵥ u) v)
    (t : ℝ) (g : V → ℝ) (hg : inner_pi pi_dist g constant_vec_one = 0) :
    inner_pi pi_dist (HeatKernel L t *ᵥ g) constant_vec_one = 0 := by
  -- Define φ(t) := ⟨HeatKernel L t *ᵥ g, 1⟩_π
  let φ : ℝ → ℝ := fun s => inner_pi pi_dist (HeatKernel L s *ᵥ g) constant_vec_one
  -- We want to show φ t = 0
  -- 
  -- Step 1: φ(0) = 0
  have hφ0 : φ 0 = 0 := by
    -- φ 0 = ⟨HeatKernel L 0 *ᵥ g, 1⟩_π = ⟨exp(0) *ᵥ g, 1⟩_π = ⟨g, 1⟩_π = 0
    show inner_pi pi_dist (HeatKernel L 0 *ᵥ g) constant_vec_one = 0
    have h1 : HeatKernel L 0 = 1 := by simp [HeatKernel, exp_zero]
    rw [h1, one_mulVec]
    exact hg
  -- 
  -- Step 2: φ'(s) = 0 for all s (using L_maps_into_one_orth)
  have hφ'_zero : ∀ s, deriv φ s = 0 := by
    intro s
    -- φ(s) = inner_pi pi_dist (HeatKernel L s *ᵥ g) constant_vec_one
    --      = ∑ v, pi_dist v * (HeatKernel L s *ᵥ g) v * 1
    --      = ∑ v, pi_dist v * (HeatKernel L s *ᵥ g) v
    -- 
    -- Define explicit function family G : V → (ℝ → ℝ)
    let G : V → (ℝ → ℝ) := fun v => fun r => pi_dist v * (HeatKernel L r *ᵥ g) v
    -- φ = ∑ v, G v as functions
    have hφ_eq : φ = ∑ v : V, G v := by
      ext r
      simp only [φ, inner_pi, constant_vec_one, Finset.sum_apply, G]
      congr 1
      ext v
      ring
    -- 
    -- Use deriv_sum to differentiate under the sum
    rw [hφ_eq, deriv_sum]
    -- Goal: ∑ v, deriv (G v) s = 0
    -- 
    -- Each deriv (G v) s = pi_dist v * deriv (fun r => (HeatKernel L r *ᵥ g) v) s
    --                    = pi_dist v * (L *ᵥ (HeatKernel L s *ᵥ g)) v
    -- by heat_semigroup_deriv (coordinatewise)
    have h_deriv_G : ∀ v : V, deriv (G v) s = pi_dist v * (L *ᵥ (HeatKernel L s *ᵥ g)) v := by
      intro v
      simp only [G]
      -- deriv (c * f) = c * deriv f
      have h_coord_diff : DifferentiableAt ℝ (fun r => (HeatKernel L r *ᵥ g) v) s := 
        HeatKernel_coord_differentiable L g v s
      rw [deriv_const_mul (pi_dist v) h_coord_diff]
      congr 1
      -- deriv (fun r => (HeatKernel L r *ᵥ g) v) s = (L *ᵥ (HeatKernel L s *ᵥ g)) v
      -- This follows from heat_semigroup_deriv coordinatewise
      have h_semigroup := heat_semigroup_deriv L g s
      -- h_semigroup : deriv (fun r => HeatKernel L r *ᵥ g) s = L *ᵥ (HeatKernel L s *ᵥ g)
      -- 
      -- The key identity: for f : ℝ → (V → ℝ), deriv (fun r => f r v) = (deriv f) v
      -- This holds because evaluation at v is a continuous linear functional
      -- In finite dimensions, this is automatic
      have h_coord_deriv : deriv (fun r => (HeatKernel L r *ᵥ g) v) s = 
             (deriv (fun r => HeatKernel L r *ᵥ g) s) v := by
        -- Use deriv_pi: if each coordinate is differentiable, then
        -- deriv φ = fun i => deriv (fun x => φ x i)
        -- So (deriv φ) v = deriv (fun x => φ x v)
        have h_all_coord_diff : ∀ w : V, DifferentiableAt ℝ (fun r => (HeatKernel L r *ᵥ g) w) s :=
          fun w => HeatKernel_coord_differentiable L g w s
        have h_pi := deriv_pi h_all_coord_diff
        -- h_pi : deriv (fun r => HeatKernel L r *ᵥ g) s = fun w => deriv (fun r => (HeatKernel L r *ᵥ g) w) s
        rw [← congr_fun h_pi v]
      rw [h_coord_deriv, h_semigroup]
    simp_rw [h_deriv_G]
    -- Goal: ∑ v, pi_dist v * (L *ᵥ (HeatKernel L s *ᵥ g)) v = 0
    -- This is inner_pi pi_dist (L *ᵥ ...) constant_vec_one = 0
    have h_L_orth := L_maps_into_one_orth L H hL1 h_H_sa hH1 h_rel (HeatKernel L s *ᵥ g)
    simp only [inner_pi, constant_vec_one] at h_L_orth
    convert h_L_orth using 1
    congr 1
    ext v
    ring
    -- 
    -- Differentiability side condition for deriv_sum
    · intro v _
      simp only [G]
      apply Differentiable.differentiableAt
      apply Differentiable.const_mul
      intro r
      exact HeatKernel_coord_differentiable L g v r
  -- 
  -- Step 3: φ' = 0 with φ(0) = 0 implies φ ≡ 0
  -- Use Mathlib's is_const_of_deriv_eq_zero: if Differentiable and deriv = 0, then constant
  have hφ_diff : Differentiable ℝ φ := by
    -- φ = ∑ v, G v where G v = fun r => pi_dist v * (HeatKernel L r *ᵥ g) v
    let G : V → (ℝ → ℝ) := fun v => fun r => pi_dist v * (HeatKernel L r *ᵥ g) v
    have hφ_eq : φ = ∑ v : V, G v := by
      ext r
      simp only [φ, inner_pi, constant_vec_one, Finset.sum_apply, G]
      congr 1; ext v; ring
    rw [hφ_eq]
    -- Each G v is differentiable
    have hG_diff : ∀ v : V, Differentiable ℝ (G v) := by
      intro v
      simp only [G]
      apply Differentiable.const_mul
      intro r
      exact HeatKernel_coord_differentiable L g v r
    exact Differentiable.sum (fun v _ => hG_diff v)
  have hφ_const : ∀ s, φ s = φ 0 := by
    intro s
    exact is_const_of_deriv_eq_zero hφ_diff hφ'_zero s 0
  -- 
  calc φ t = φ 0 := hφ_const t
    _ = 0 := hφ0

/--
**Pillar 2 Interface: `EnvelopeSpec`**
A typeclass defining the contract for a transient envelope `B(t)`.
-/
class EnvelopeSpec (L H : Matrix V V ℝ) (pi_dist : V → ℝ) where
  B : ℝ → ℝ
  B_zero : B 0 = 1
  r : ℝ
  r_ge_gap : r ≥ SpectralGap_pi pi_dist H
  /--
  The core bounding inequality: ‖e^{tL} P_⊥‖_π ≤ B(t) * e^{-rt}.
  P is the projector onto (span{1})⊥ in the L²(pi) space.
  -/
  bound :
    ∀ t ≥ 0, ∀ (h_pos : ∀ v, 0 < pi_dist v) (P : (V → ℝ) →ₗ[ℝ] (V → ℝ)),
    opNorm_pi pi_dist h_pos (toLin' (HeatKernel L t) ∘ₗ P) ≤ B t * Real.exp (-r * t)

end FHDT
