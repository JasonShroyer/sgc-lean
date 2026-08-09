import SGC.Spectral.Envelope
import SGC.Spectral.Envelope.ODE
import SGC.Spectral.Core.Assumptions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open Matrix Real ContinuousLinearMap Filter Topology Finset LinearMap NormedSpace

namespace SGC.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inner product of 1 with itself is 1 under π. -/
lemma inner_pi_one_one {pi_dist : V → ℝ} (h_sum : ∑ x, pi_dist x = 1) :
    inner_pi pi_dist (fun _ => 1) (fun _ => 1) = 1 := by
  simp only [inner_pi, mul_one]
  exact h_sum

/-- **Self-Adjointness of P_ortho_pi**: ⟨Pu, v⟩_π = ⟨u, Pv⟩_π.
    This is the key algebraic property showing P is orthogonal w.r.t. inner_pi. -/
lemma P_ortho_pi_is_selfAdj {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1) :
    ∀ u v, inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) u) v = 
           inner_pi pi_dist u ((P_ortho_pi pi_dist h_sum hπ) v) := by
  intro u v
  -- Expand P = id - ⟨·,1⟩_π ⊗ 1
  unfold P_ortho_pi
  simp only [LinearMap.sub_apply, LinearMap.id_apply, 
             LinearMap.smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS: ⟨u - ⟨u,1⟩_π · 1, v⟩_π = ⟨u,v⟩_π - ⟨u,1⟩_π · ⟨1,v⟩_π
  -- RHS: ⟨u, v - ⟨v,1⟩_π · 1⟩_π = ⟨u,v⟩_π - ⟨v,1⟩_π · ⟨u,1⟩_π
  -- These are equal by commutativity of inner_pi
  rw [inner_pi_sub_left, inner_pi_sub_right]
  rw [inner_pi_smul_left, inner_pi_smul_right]
  -- Now we have: ⟨u,v⟩ - ⟨u,1⟩ * ⟨1,v⟩ = ⟨u,v⟩ - ⟨v,1⟩ * ⟨u,1⟩
  -- Use inner_pi_comm: ⟨1,v⟩ = ⟨v,1⟩
  rw [inner_pi_comm (fun _ => (1:ℝ)) v]
  ring

/-- **Idempotence of P_ortho_pi**: P ∘ P = P.
    This shows P is a true projection operator. -/
lemma P_ortho_pi_idem {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1) :
    (P_ortho_pi pi_dist h_sum hπ) ∘ₗ (P_ortho_pi pi_dist h_sum hπ) = P_ortho_pi pi_dist h_sum hπ := by
  -- Prove equality of linear maps by showing they agree on all inputs
  apply LinearMap.ext
  intro f
  unfold P_ortho_pi
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
             LinearMap.smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk]
  -- At this point we have P (P f) expanded. Let α := ⟨f,1⟩_π.
  -- Then P f = f - α · 1.
  -- So P (P f) = (f - α·1) - ⟨f - α·1, 1⟩_π · 1.
  -- Compute ⟨f - α·1, 1⟩_π = ⟨f,1⟩_π - α · ⟨1,1⟩_π = α - α · 1 = 0.
  -- Hence P (P f) = f - α·1 = P f.
  
  -- First, show ⟨1,1⟩_π = 1
  have h_one_inner : inner_pi pi_dist (fun _ => (1:ℝ)) (fun _ => 1) = 1 := 
    inner_pi_one_one h_sum
  
  -- Simplify using bilinearity
  rw [inner_pi_sub_left, inner_pi_smul_left, h_one_inner]
  -- Now we have: f - α·1 - (α - α * 1) • 1 = f - α·1 - 0 • 1 = f - α·1
  simp only [mul_one, sub_self, zero_smul, sub_zero]

/-- P_ortho_pi projects onto the orthogonal complement of constants:
    ⟨P u, 1⟩_π = 0 for all u. -/
lemma P_ortho_pi_orthogonal_to_one {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) 
    (h_sum : ∑ x, pi_dist x = 1) (u : V → ℝ) :
    inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) u) (fun _ => 1) = 0 := by
  unfold P_ortho_pi
  simp only [LinearMap.sub_apply, LinearMap.id_apply,
             LinearMap.smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [inner_pi_sub_left, inner_pi_smul_left]
  have h_one_inner : inner_pi pi_dist (fun _ => (1:ℝ)) (fun _ => 1) = 1 := 
    inner_pi_one_one h_sum
  rw [h_one_inner]
  ring

--------------------------------------------------------------------------------
-- Trajectory and Energy Definitions for Lyapunov Method
--------------------------------------------------------------------------------

/-- Projected trajectory: u(t) = e^{tL} (P_ortho f).
    This is the solution of the projected heat equation starting from P f. -/
def u_traj {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) : V → ℝ :=
  (toLin' (HeatKernel L t)) ((P_ortho_pi pi_dist h_sum hπ) f)

/-- Energy along the trajectory: E(t) = ‖u(t)‖²_π.
    This is the Lyapunov function for the decay analysis. -/
def E_traj {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) : ℝ :=
  norm_sq_pi pi_dist (u_traj hπ h_sum L f t)

/-- E_traj expressed as an explicit finite sum.
    This form makes differentiation straightforward. -/
lemma E_traj_eq_sum {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) :
    E_traj hπ h_sum L f t = ∑ v, pi_dist v * (u_traj hπ h_sum L f t v) ^ 2 := by
  unfold E_traj
  exact norm_sq_pi_eq_sum pi_dist (u_traj hπ h_sum L f t)

/-- E_traj is non-negative (since it's a sum of squares). -/
lemma E_traj_nonneg {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) :
    0 ≤ E_traj hπ h_sum L f t := by
  unfold E_traj
  exact norm_sq_pi_nonneg pi_dist hπ (u_traj hπ h_sum L f t)

/-- norm_pi of trajectory relates to square root of E_traj. -/
lemma norm_pi_u_traj {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) :
    norm_pi pi_dist (u_traj hπ h_sum L f t) = Real.sqrt (E_traj hπ h_sum L f t) := by
  unfold E_traj norm_pi
  rfl

--------------------------------------------------------------------------------
-- Differentiability of Heat Kernel and Trajectory
--------------------------------------------------------------------------------

-- Note: HeatKernel_differentiable as a matrix-valued function is not needed.
-- We use the stronger coordinate-level differentiability via HeatKernel_coord_differentiable
-- which is already proved in SGC.Spectral.Envelope.

/-- Each coordinate of u_traj is differentiable in t.
    u_traj t v = (HeatKernel L t *ᵥ P f) v is a composition of:
    - t ↦ HeatKernel L t (differentiable)
    - matrix-vector multiplication (linear)
    - coordinate extraction (linear) -/
lemma u_traj_coord_differentiable {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (v : V) :
    Differentiable ℝ (fun t => u_traj hπ h_sum L f t v) := by
  -- u_traj t v = (HeatKernel L t *ᵥ P f) v = (toLin' (HeatKernel L t) (P f)) v
  -- Let g = P_ortho_pi f, then u_traj t = HeatKernel L t *ᵥ g
  let g : V → ℝ := (P_ortho_pi pi_dist h_sum hπ) f
  -- u_traj hπ h_sum L f t v = (HeatKernel L t *ᵥ g) v
  have h_eq : (fun t => u_traj hπ h_sum L f t v) = (fun t => (HeatKernel L t *ᵥ g) v) := by
    ext t
    simp only [u_traj, toLin'_apply, g]
  rw [h_eq]
  -- Now use HeatKernel_coord_differentiable from SGC.Spectral.Envelope
  intro t
  exact HeatKernel_coord_differentiable L g v t

/-- Derivative of a coordinate of u_traj satisfies the heat equation ODE:
    d/dt (u_traj t v) = (L *ᵥ u_traj t) v
    
    Proof idea: d/dt (exp(tL) *ᵥ u₀) = L * exp(tL) *ᵥ u₀ = L *ᵥ (exp(tL) *ᵥ u₀)
    using that exp(tL) commutes with L. -/
lemma u_traj_coord_deriv {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (v : V) (t : ℝ) :
    deriv (fun s => u_traj hπ h_sum L f s v) t = (L *ᵥ u_traj hπ h_sum L f t) v := by
  -- Let g = P_ortho_pi f, then u_traj t = HeatKernel L t *ᵥ g
  let g : V → ℝ := (P_ortho_pi pi_dist h_sum hπ) f
  -- u_traj s v = (HeatKernel L s *ᵥ g) v
  have h_eq_fun : (fun s => u_traj hπ h_sum L f s v) = (fun s => (HeatKernel L s *ᵥ g) v) := by
    ext s
    simp only [u_traj, toLin'_apply, g]
  rw [h_eq_fun]
  -- RHS: (L *ᵥ u_traj t) v = (L *ᵥ (HeatKernel L t *ᵥ g)) v
  have h_rhs : (L *ᵥ u_traj hπ h_sum L f t) v = (L *ᵥ (HeatKernel L t *ᵥ g)) v := by
    simp only [u_traj, toLin'_apply, g]
  rw [h_rhs]
  -- Use heat_semigroup_deriv: deriv (fun s => HeatKernel L s *ᵥ g) t = L *ᵥ (HeatKernel L t *ᵥ g)
  have h_semigroup := heat_semigroup_deriv L g t
  -- Use deriv_pi to pass from vector derivative to coordinate derivative
  have h_all_diff : ∀ w : V, DifferentiableAt ℝ (fun s => (HeatKernel L s *ᵥ g) w) t :=
    fun w => HeatKernel_coord_differentiable L g w t
  have h_pi := deriv_pi h_all_diff
  -- h_pi : deriv (fun s => HeatKernel L s *ᵥ g) t = fun w => deriv (fun s => (HeatKernel L s *ᵥ g) w) t
  -- Apply at v: (deriv ...) v = deriv (fun s => (HeatKernel L s *ᵥ g) v) t
  have h_coord : deriv (fun s => (HeatKernel L s *ᵥ g) v) t = 
                 (deriv (fun s => HeatKernel L s *ᵥ g) t) v := by
    exact congrFun h_pi v |>.symm
  rw [h_coord, h_semigroup]

/-- The vector-valued derivative of u_traj: d/dt u_traj t = L *ᵥ u_traj t -/
lemma u_traj_deriv_eq_L_mul {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) :
    (fun v => deriv (fun s => u_traj hπ h_sum L f s v) t) = L *ᵥ u_traj hπ h_sum L f t := by
  ext v
  exact u_traj_coord_deriv hπ h_sum L f v t

--------------------------------------------------------------------------------
-- Energy Derivative Formulas
--------------------------------------------------------------------------------

/-- E_traj is differentiable (needed for applying Grönwall).
    
    **Proof idea:** E_traj t = ∑ v, π(v) * (u_traj t v)² is a finite sum.
    Each summand is differentiable:
    - u_traj t v is differentiable in t (from u_traj_coord_differentiable)
    - (u_traj t v)² is differentiable (composition with x²)
    - π(v) * (...) is differentiable (constant multiple)
    Finite sums of differentiable functions are differentiable.
    
    The underlying calculus follows from u_traj_coord_differentiable and
    standard finite-sum calculus lemmas. -/
lemma E_traj_differentiable {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) 
    (h_sum : ∑ x, pi_dist x = 1) (L : Matrix V V ℝ) (f : V → ℝ) :
    Differentiable ℝ (E_traj hπ h_sum L f) := by
  -- Define the summand functions explicitly as a family F : V → (ℝ → ℝ)
  let F : V → (ℝ → ℝ) := fun v => fun t => pi_dist v * (u_traj hπ h_sum L f t v) ^ 2
  -- E_traj = ∑ v, F v as functions (using funext)
  have hE_eq : E_traj hπ h_sum L f = ∑ v : V, F v := by
    ext t
    simp only [E_traj_eq_sum, Finset.sum_apply, F]
  rw [hE_eq]
  -- Each summand is differentiable
  have hF_diff : ∀ v : V, Differentiable ℝ (F v) := by
    intro v
    simp only [F]
    apply Differentiable.const_mul
    apply Differentiable.pow
    exact u_traj_coord_differentiable hπ h_sum L f v
  -- Finite sum of differentiable functions is differentiable
  exact Differentiable.sum (fun v _ => hF_diff v)

/-- Derivative formula for E_traj in terms of inner product.
    E'(t) = 2 * ⟨u(t), u'(t)⟩_π
    
    **Proof idea:** Differentiate E(t) = ∑ᵥ π(v) u(t,v)² under the sum:
    - d/dt [π(v) u²] = π(v) · 2u · u' by chain rule
    - Sum over v: E'(t) = 2 ∑ᵥ π(v) u(t,v) u'(t,v) = 2⟨u(t), u'(t)⟩_π -/
lemma E_traj_deriv_formula {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) :
    deriv (E_traj hπ h_sum L f) t = 
      2 * inner_pi pi_dist (u_traj hπ h_sum L f t) 
                           (fun v => deriv (fun s => u_traj hπ h_sum L f s v) t) := by
  -- Define the summand functions explicitly as a family F : V → (ℝ → ℝ)
  let F : V → (ℝ → ℝ) := fun v => fun s => pi_dist v * (u_traj hπ h_sum L f s v) ^ 2
  -- E_traj = ∑ v, F v as functions
  have hE_eq : E_traj hπ h_sum L f = ∑ v : V, F v := by
    ext s
    simp only [E_traj_eq_sum, Finset.sum_apply, F]
  -- 
  -- Step 1: deriv of a finite sum = sum of derivs
  rw [hE_eq, deriv_sum]
  -- Goal: ∑ v, deriv (F v) t = 2 * inner_pi ...
  -- 
  -- Step 2: Compute deriv (F v) for each v using chain rule
  -- F v = fun s => π(v) * (u s v)², so
  -- deriv (F v) t = π(v) * 2 * (u t v) * deriv (fun s => u s v) t
  have h_deriv_F : ∀ v : V, deriv (F v) t = 
      pi_dist v * (2 * u_traj hπ h_sum L f t v * deriv (fun s => u_traj hπ h_sum L f s v) t) := by
    intro v
    simp only [F]
    -- deriv (c * f²) = c * deriv(f²) = c * 2 * f * deriv f
    have hu_diff : DifferentiableAt ℝ (fun s => u_traj hπ h_sum L f s v) t :=
      (u_traj_coord_differentiable hπ h_sum L f v).differentiableAt
    -- Define u_v for clarity
    let u_v := fun s => u_traj hπ h_sum L f s v
    -- deriv (c * u²) = c * deriv(u²)
    have hu2_diff : DifferentiableAt ℝ (fun s => (u_v s) ^ 2) t := hu_diff.pow 2
    have h1 : deriv (fun s => pi_dist v * (u_v s) ^ 2) t = 
              pi_dist v * deriv (fun s => (u_v s) ^ 2) t := 
      deriv_const_mul (pi_dist v) hu2_diff
    rw [h1]
    congr 1
    -- deriv (u²) = 2 * u * u' using HasDerivAt
    have hu_hasderiv : HasDerivAt u_v (deriv u_v t) t := hu_diff.hasDerivAt
    have h_sq : HasDerivAt (fun s => (u_v s) ^ 2) (2 * u_v t * deriv u_v t) t := by
      have := hu_hasderiv.pow 2
      simp only [Nat.add_one_sub_one, pow_one] at this
      exact this
    exact h_sq.deriv
  simp_rw [h_deriv_F]
  -- Goal: ∑ v, π(v) * (2 * u(t,v) * u'(t,v)) = 2 * inner_pi ...
  -- 
  -- Step 3: Recognize as 2 * inner_pi by expanding inner_pi
  simp only [inner_pi]
  -- Goal: ∑ v, π(v) * (2 * u(t,v) * u'(t,v)) = 2 * ∑ v, π(v) * u(t,v) * u'(t,v)
  rw [Finset.mul_sum]
  congr 1
  ext v
  ring
  -- 
  -- Differentiability side condition for deriv_sum
  · intro v _
    simp only [F]
    apply Differentiable.differentiableAt
    apply Differentiable.const_mul
    apply Differentiable.pow
    exact u_traj_coord_differentiable hπ h_sum L f v

/-- Key formula: E'(t) = 2 * ⟨u(t), L *ᵥ u(t)⟩_π
    Combines E_traj_deriv_formula with u_traj_deriv_eq_L_mul. -/
lemma E_traj_deriv_eq_inner_L {pi_dist : V → ℝ}
    (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L : Matrix V V ℝ) (f : V → ℝ) (t : ℝ) :
    deriv (E_traj hπ h_sum L f) t = 
      2 * inner_pi pi_dist (u_traj hπ h_sum L f t) (L *ᵥ u_traj hπ h_sum L f t) := by
  rw [E_traj_deriv_formula hπ h_sum L f t]
  -- Replace the derivative function with L *ᵥ u_traj using u_traj_deriv_eq_L_mul
  have h := u_traj_deriv_eq_L_mul hπ h_sum L f t
  -- h : (fun v => deriv ...) = L *ᵥ u_traj
  simp only [h]

--------------------------------------------------------------------------------
-- Energy Derivative Bound (Key Lemma for Sector Envelope)
--------------------------------------------------------------------------------

/-- **Energy derivative bound using sector relation**:
    
    Under the sector relation between L and H, and with H having a spectral gap
    on 1⊥, the energy E(t) = ‖e^{tL} P f‖²_π satisfies:
    
      E'(t) ≤ -2 * gap * E(t)
    
    **Proof sketch:**
    1. E'(t) = 2⟨u(t), L *ᵥ u(t)⟩_π (from E_traj_deriv_eq_inner_L)
    2. By the sector relation with v = u: 2⟨Lu, u⟩_π = -2⟨Hu, u⟩_π
    3. By the spectral gap coercivity: ⟨Hu, u⟩_π ≥ gap * ‖u‖²_π for u ⊥ 1
    4. Hence E'(t) = -2⟨Hu, u⟩_π ≤ -2 * gap * E(t)
-/
lemma E_traj_deriv_sector
    [Nontrivial V] {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
    (L H : Matrix V V ℝ)
    (hL1 : L *ᵥ constant_vec_one = 0)  -- Stationarity: L kills constants
    (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
    (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
    (h_constH : H *ᵥ constant_vec_one = 0)
    (h_gap : 0 < SpectralGap_pi pi_dist H)
    (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) = 
                    -2 * inner_pi pi_dist (H *ᵥ u) v)
    (f : V → ℝ) :
    ∀ t ≥ 0, deriv (E_traj hπ h_sum L f) t ≤ -2 * (SpectralGap_pi pi_dist H) * (E_traj hπ h_sum L f t) := by
  intro t _ht
  -- Let u := u_traj t for convenience
  let u := u_traj hπ h_sum L f t
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 1: E'(t) = 2⟨u(t), L *ᵥ u(t)⟩_π
  -- ════════════════════════════════════════════════════════════════════════════
  rw [E_traj_deriv_eq_inner_L hπ h_sum L f t]
  
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 2: Use sector relation to rewrite ⟨Lu, u⟩_π in terms of H
  -- Setting v := u in h_rel: ⟨Lu, u⟩ + ⟨u, Lu⟩ = -2⟨Hu, u⟩
  -- By symmetry of inner_pi: 2⟨Lu, u⟩ = -2⟨Hu, u⟩, so ⟨Lu, u⟩ = -⟨Hu, u⟩
  -- ════════════════════════════════════════════════════════════════════════════
  have h_sector_u : inner_pi pi_dist u (L *ᵥ u) = -inner_pi pi_dist (H *ᵥ u) u := by
    have h1 := h_rel u u
    -- h1 : ⟨Lu, u⟩ + ⟨u, Lu⟩ = -2⟨Hu, u⟩
    have h_sym : inner_pi pi_dist (L *ᵥ u) u = inner_pi pi_dist u (L *ᵥ u) := inner_pi_comm (L *ᵥ u) u
    -- So 2⟨u, Lu⟩ = -2⟨Hu, u⟩
    have h2 : 2 * inner_pi pi_dist u (L *ᵥ u) = -2 * inner_pi pi_dist (H *ᵥ u) u := by
      calc 2 * inner_pi pi_dist u (L *ᵥ u) 
          = inner_pi pi_dist (L *ᵥ u) u + inner_pi pi_dist u (L *ᵥ u) := by rw [h_sym]; ring
        _ = -2 * inner_pi pi_dist (H *ᵥ u) u := h1
    linarith
  
  -- So E'(t) = 2 * (-⟨Hu, u⟩) = -2⟨Hu, u⟩
  calc 2 * inner_pi pi_dist u (L *ᵥ u) 
      = 2 * (-inner_pi pi_dist (H *ᵥ u) u) := by rw [h_sector_u]
    _ = -2 * inner_pi pi_dist (H *ᵥ u) u := by ring
    _ ≤ -2 * (SpectralGap_pi pi_dist H * norm_sq_pi pi_dist u) := by
        -- ════════════════════════════════════════════════════════════════════════════
        -- Step 3: Use spectral gap coercivity: ⟨Hu, u⟩ ≥ gap * ‖u‖²
        -- u is orthogonal to 1 because u = HeatKernel L t *ᵥ (P f), P f ⊥ 1,
        -- and HeatKernel preserves 1⊥ (by stationarity hL1)
        -- ════════════════════════════════════════════════════════════════════════════
        have h_u_orth : inner_pi pi_dist u constant_vec_one = 0 := by
          -- u = u_traj t = HeatKernel L t *ᵥ (P_ortho_pi f)
          -- P_ortho_pi f ⊥ 1 by P_ortho_pi_orthogonal_to_one
          -- HeatKernel preserves 1⊥ by HeatKernel_maps_one_orth_to_one_orth
          have h_Pf_orth : inner_pi pi_dist (P_ortho_pi pi_dist h_sum hπ f) constant_vec_one = 0 :=
            P_ortho_pi_orthogonal_to_one hπ h_sum f
          exact HeatKernel_maps_one_orth_to_one_orth L H hL1 h_sa h_constH h_rel t 
                  (P_ortho_pi pi_dist h_sum hπ f) h_Pf_orth
        have h_coercivity := SpectralGap_coercivity hπ H h_sa h_psd h_constH h_gap u h_u_orth
        -- h_coercivity : ⟨Hu, u⟩ ≥ gap * ‖u‖²
        -- We need: -2 * ⟨Hu, u⟩ ≤ -2 * gap * ‖u‖²
        -- i.e., ⟨Hu, u⟩ ≥ gap * ‖u‖² (which is h_coercivity)
        linarith
    _ = -2 * SpectralGap_pi pi_dist H * norm_sq_pi pi_dist u := by ring
    _ = -2 * SpectralGap_pi pi_dist H * E_traj hπ h_sum L f t := by
        -- E_traj t = norm_sq_pi (u_traj t) by definition
        unfold E_traj
        rfl

--------------------------------------------------------------------------------
-- Main Sector Envelope Theorem
--------------------------------------------------------------------------------

/--
**Pillar 2: Canonical Sector Envelope Bound**
This theorem proves that if the system satisfies the spectral gap conditions,
the projected semigroup contracts purely exponentially:
‖e^{tL} P‖_π ≤ e^{-λ_{gap} t}

**Proof outline:**
1. For any f, let u(t) = e^{tL} P f and E(t) = ‖u(t)‖²_π
2. By E_traj_deriv_sector: E'(t) ≤ -2 * gap * E(t)
3. By energy_decay_implies_norm_decay: E(t) ≤ E(0) * e^{-2*gap*t}
4. Taking square roots: ‖u(t)‖_π ≤ ‖u(0)‖_π * e^{-gap*t} = ‖P f‖_π * e^{-gap*t}
5. Since P is an orthogonal projection: ‖P f‖_π ≤ ‖f‖_π
6. Hence ‖e^{tL} P f‖_π ≤ e^{-gap*t} * ‖f‖_π
7. Taking sup over ‖f‖_π ≤ 1 gives ‖e^{tL} P‖_π ≤ e^{-gap*t}
-/
lemma sector_envelope_bound_canonical
  [Nontrivial V] {pi_dist : V → ℝ} (hπ : ∀ x, 0 < pi_dist x) (h_sum : ∑ x, pi_dist x = 1)
  (L H : Matrix V V ℝ)
  (hL1 : L *ᵥ constant_vec_one = 0)  -- Stationarity
  (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
  (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
  (h_constH : H *ᵥ constant_vec_one = 0)
  (h_gap : 0 < SpectralGap_pi pi_dist H)
  (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) = -2 * inner_pi pi_dist (H *ᵥ u) v)
  (t : ℝ) (ht : 0 ≤ t) :
  opNorm_pi pi_dist hπ (toLin' (exp ℝ (t • L)) ∘ₗ (P_ortho_pi pi_dist h_sum hπ))
  ≤ Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
  -- ════════════════════════════════════════════════════════════════════════════
  -- The operator is T_t = toLin' (HeatKernel L t) ∘ₗ P_ortho_pi
  -- We show: for all f, ‖T_t f‖_π ≤ e^{-gap*t} * ‖f‖_π
  -- Then take sup over unit ball to get opNorm bound.
  -- ════════════════════════════════════════════════════════════════════════════
  
  -- Relate exp ℝ (t • L) to HeatKernel
  have h_exp_eq : exp ℝ (t • L) = HeatKernel L t := rfl
  rw [h_exp_eq]
  
  -- The operator T_t applied to f gives u_traj hπ h_sum L f t
  -- For any f, ‖T_t f‖_π = ‖u_traj t‖_π = sqrt(E_traj t)
  
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 1: For any f, apply Grönwall via energy_decay_implies_norm_decay
  -- ════════════════════════════════════════════════════════════════════════════
  
  -- Operator norm definition: opNorm_pi is the inf of constants c such that
  -- ‖A f‖_π ≤ c * ‖f‖_π for all f.
  -- We show e^{-gap*t} works by showing the pointwise bound for all f.
  
  apply opNorm_pi_le_of_bound pi_dist hπ _ (Real.exp (-(SpectralGap_pi pi_dist H) * t)) (Real.exp_nonneg _)
  intro f
  
  -- ‖T_t f‖_π = ‖u_traj t‖_π = norm_pi (u_traj hπ h_sum L f t)
  have h_Tf_eq : (toLin' (HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) f = 
                 u_traj hπ h_sum L f t := by
    simp only [LinearMap.comp_apply, u_traj, toLin'_apply]
  rw [h_Tf_eq]
  
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 2: Apply Grönwall to E_traj
  -- ════════════════════════════════════════════════════════════════════════════
  
  -- E_traj satisfies E' ≤ -2*gap*E by E_traj_deriv_sector
  have h_deriv_bound : ∀ s ≥ 0, deriv (E_traj hπ h_sum L f) s ≤ 
                       -2 * SpectralGap_pi pi_dist H * E_traj hπ h_sum L f s :=
    E_traj_deriv_sector hπ h_sum L H hL1 h_sa h_psd h_constH h_gap h_rel f
  
  -- Apply energy_decay_implies_norm_decay
  have h_E_nonneg : ∀ s ≥ 0, 0 ≤ E_traj hπ h_sum L f s := fun s _ => E_traj_nonneg hπ h_sum L f s
  have h_norm_decay := energy_decay_implies_norm_decay h_gap 
                       (E_traj_differentiable hπ h_sum L f)
                       h_E_nonneg
                       h_deriv_bound t ht
  -- h_norm_decay : sqrt(E_traj t) ≤ sqrt(E_traj 0) * exp(-gap * t)
  
  -- Convert: ‖u_traj t‖_π = sqrt(E_traj t) by norm_pi_u_traj
  rw [norm_pi_u_traj hπ h_sum L f t]
  
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 3: Bound sqrt(E_traj 0) ≤ ‖f‖_π using projection contraction
  -- ════════════════════════════════════════════════════════════════════════════
  
  -- E_traj 0 = ‖u_traj 0‖²_π = ‖P f‖²_π
  -- At t = 0, HeatKernel L 0 = 1, so u_traj 0 = P f
  have h_u0 : u_traj hπ h_sum L f 0 = (P_ortho_pi pi_dist h_sum hπ) f := by
    simp only [u_traj, toLin'_apply]
    rw [HeatKernel_at_zero L]
    simp only [Matrix.one_mulVec]
  
  have h_E0 : E_traj hπ h_sum L f 0 = norm_sq_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) := by
    simp only [E_traj, h_u0]
  
  -- Projection contraction: ‖P f‖_π ≤ ‖f‖_π for orthogonal projection P
  -- Standard fact: for idempotent self-adjoint operator in an inner product space
  have h_P_contr : norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) ≤ norm_pi pi_dist f := by
    -- ‖P f‖² = ⟨Pf, Pf⟩ = ⟨Pf, f⟩ (using self-adjointness and idempotence)
    --        ≤ ‖Pf‖ * ‖f‖ (by Cauchy-Schwarz)
    -- So ‖Pf‖ ≤ ‖f‖ (divide by ‖Pf‖ if nonzero)
    by_cases h_Pf_zero : (P_ortho_pi pi_dist h_sum hπ) f = 0
    · -- If Pf = 0, then ‖Pf‖ = 0 ≤ ‖f‖
      simp only [h_Pf_zero, norm_pi, norm_sq_pi, inner_pi_zero_left]
      simp only [Real.sqrt_zero]
      exact Real.sqrt_nonneg _
    · have h_norm_Pf_pos : 0 < norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) := by
        rw [norm_pi]
        apply Real.sqrt_pos_of_pos
        exact norm_sq_pi_pos hπ h_Pf_zero
      -- Use self-adjointness and idempotence
      have h_sa_P := P_ortho_pi_is_selfAdj hπ h_sum
      have h_idem := P_ortho_pi_idem hπ h_sum
      -- P(Pf) = Pf by idempotence
      have h_PPf : (P_ortho_pi pi_dist h_sum hπ) ((P_ortho_pi pi_dist h_sum hπ) f) = 
                   (P_ortho_pi pi_dist h_sum hπ) f := by
        have h := h_idem
        calc (P_ortho_pi pi_dist h_sum hπ) ((P_ortho_pi pi_dist h_sum hπ) f)
            = (P_ortho_pi pi_dist h_sum hπ ∘ₗ P_ortho_pi pi_dist h_sum hπ) f := rfl
          _ = (P_ortho_pi pi_dist h_sum hπ) f := by rw [h]
      -- ⟨Pf, Pf⟩ = ⟨Pf, f⟩ via self-adjoint and idempotent
      have h_inner_eq : inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) 
                                        ((P_ortho_pi pi_dist h_sum hπ) f) =
                        inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) f := by
        calc inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) ((P_ortho_pi pi_dist h_sum hπ) f)
            = inner_pi pi_dist f ((P_ortho_pi pi_dist h_sum hπ) ((P_ortho_pi pi_dist h_sum hπ) f)) := by
                rw [inner_pi_comm, h_sa_P]
          _ = inner_pi pi_dist f ((P_ortho_pi pi_dist h_sum hπ) f) := by rw [h_PPf]
          _ = inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) f := inner_pi_comm _ _
      -- Now: ‖Pf‖² = ⟨Pf, f⟩ ≤ ‖Pf‖ * ‖f‖ by Cauchy-Schwarz
      have h_cs := cauchy_schwarz_pi pi_dist hπ ((P_ortho_pi pi_dist h_sum hπ) f) f
      -- h_cs : |⟨Pf, f⟩| ≤ ‖Pf‖ * ‖f‖
      -- Since ⟨Pf, f⟩ = ‖Pf‖² ≥ 0, we have ⟨Pf, f⟩ = |⟨Pf, f⟩| ≤ ‖Pf‖ * ‖f‖
      have h_inner_nonneg : 0 ≤ inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) f := by
        rw [← h_inner_eq]
        exact norm_sq_pi_nonneg pi_dist hπ _
      -- ‖Pf‖² ≤ ‖Pf‖ * ‖f‖
      have h_sq_ineq : norm_sq_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) ≤ 
                       norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) * norm_pi pi_dist f := by
        unfold norm_sq_pi
        rw [h_inner_eq]
        calc inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) f 
            = |inner_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) f| := by
                rw [abs_of_nonneg h_inner_nonneg]
          _ ≤ norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) * norm_pi pi_dist f := h_cs
      -- norm_sq = norm², so norm² ≤ norm * ‖f‖ implies norm ≤ ‖f‖
      have h_norm_sq_eq : norm_sq_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) = 
                          (norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f))^2 := by
        rw [norm_pi, Real.sq_sqrt (norm_sq_pi_nonneg pi_dist hπ _)]
      rw [h_norm_sq_eq] at h_sq_ineq
      -- x² ≤ x * y and x > 0 implies x ≤ y
      have h_pos : 0 < norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) := h_norm_Pf_pos
      calc norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) 
          = (norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f))^2 / 
            (norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f)) := by
              field_simp [ne_of_gt h_pos]
        _ ≤ (norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) * norm_pi pi_dist f) / 
            (norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f)) := by
              apply div_le_div_of_nonneg_right h_sq_ineq (le_of_lt h_pos)
        _ = norm_pi pi_dist f := by field_simp [ne_of_gt h_pos]
  
  -- sqrt(E_traj 0) = ‖P f‖_π
  have h_sqrt_E0 : Real.sqrt (E_traj hπ h_sum L f 0) = 
                   norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) := by
    rw [h_E0]
    simp only [norm_pi]
  
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 4: Combine: ‖u_traj t‖_π ≤ e^{-gap*t} * ‖f‖_π
  -- ════════════════════════════════════════════════════════════════════════════
  
  calc Real.sqrt (E_traj hπ h_sum L f t) 
      ≤ Real.sqrt (E_traj hπ h_sum L f 0) * Real.exp (-(SpectralGap_pi pi_dist H) * t) := h_norm_decay
    _ = norm_pi pi_dist ((P_ortho_pi pi_dist h_sum hπ) f) * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
        rw [h_sqrt_E0]
    _ ≤ norm_pi pi_dist f * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
        apply mul_le_mul_of_nonneg_right h_P_contr (Real.exp_nonneg _)
    _ = Real.exp (-(SpectralGap_pi pi_dist H) * t) * norm_pi pi_dist f := by ring

end SGC.Spectral
