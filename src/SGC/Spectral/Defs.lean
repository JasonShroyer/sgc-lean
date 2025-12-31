import SGC.Spectral.Envelope
import SGC.Spectral.Envelope.Sector
import SGC.Spectral.Core.Assumptions
import SGC.Spectral.Core.Projector
import SGC.Spectral.Diagonal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Matrix Real Finset LinearMap

namespace SGC.Spectral

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {L H : Matrix V V ℝ} {pi_dist : V → ℝ} {ε : ℝ}

/-- The normalized return probability observable: 1 - K_xx(t)/π_x. -/
def K_norm (L : Matrix V V ℝ) (t : ℝ) (x : V) (pix : ℝ) : ℝ :=
  1 - (HeatKernel L t) x x / pix

/-- The **expected log return probability**: E_π[log(1 - K_xx(t)/π_x + ε)].
    
    This observable tracks the expected logarithmic deviation of return 
    probabilities from stationary values. -/
def expected_log_return_prob (L : Matrix V V ℝ) (pi_dist : V → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  ∑ x, pi_dist x * Real.log (K_norm L t x (pi_dist x) + ε)

/-- The **stability flow** β(t): time derivative of the expected log return probability.
    
    This flow measures the rate of change of the expected log-observable,
    providing a measure of how quickly the system approaches stationarity. -/
def stability_flow (L : Matrix V V ℝ) (pi_dist : V → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  deriv (expected_log_return_prob L pi_dist ε) t

--------------------------------------------------------------------------------
-- Helper: Differentiability of K_norm at a fixed state x
--------------------------------------------------------------------------------

/-- The heat kernel diagonal is differentiable in t. -/
lemma HeatKernel_diag_differentiable (L : Matrix V V ℝ) (x : V) :
    Differentiable ℝ (fun t => (HeatKernel L t) x x) := by
  intro t
  -- (HeatKernel L t) x x = (HeatKernel L t *ᵥ e_x) x where e_x is the standard basis
  let e_x : V → ℝ := fun v => if v = x then 1 else 0
  have h_eq : (fun s => (HeatKernel L s) x x) = (fun s => (HeatKernel L s *ᵥ e_x) x) := by
    ext s
    simp only [mulVec, dotProduct, e_x]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [if_neg hy]
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  rw [h_eq]
  exact HeatKernel_coord_differentiable L e_x x t

/-- K_norm is differentiable in t (for fixed x and pi_x > 0). -/
lemma K_norm_differentiable (L : Matrix V V ℝ) (x : V) (pix : ℝ) (hpix : pix > 0) :
    Differentiable ℝ (fun t => K_norm L t x pix) := by
  unfold K_norm
  apply Differentiable.sub
  · exact differentiable_const 1
  · apply Differentiable.div_const
    exact HeatKernel_diag_differentiable L x

/-- The derivative of K_norm involves the heat kernel derivative. -/
lemma deriv_K_norm (L : Matrix V V ℝ) (x : V) (pix : ℝ) (hpix : pix > 0) (t : ℝ) :
    deriv (fun s => K_norm L s x pix) t = 
    -(deriv (fun s => (HeatKernel L s) x x) t) / pix := by
  -- K_norm L s x pix = 1 - (HeatKernel L s) x x / pix
  have h_diag_diff : Differentiable ℝ (fun s => (HeatKernel L s) x x) := 
    HeatKernel_diag_differentiable L x
  -- Compute directly using HasDerivAt
  have h_const : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h_diag : HasDerivAt (fun s => (HeatKernel L s) x x) 
                           (deriv (fun s => (HeatKernel L s) x x) t) t := 
    (h_diag_diff t).hasDerivAt
  have h_div : HasDerivAt (fun s => (HeatKernel L s) x x / pix) 
                          ((deriv (fun s => (HeatKernel L s) x x) t) / pix) t := by
    have := h_diag.div_const pix
    convert this using 1
  have h_sub : HasDerivAt (fun s => 1 - (HeatKernel L s) x x / pix) 
                          (0 - (deriv (fun s => (HeatKernel L s) x x) t) / pix) t := 
    h_const.sub h_div
  have h_K_eq : (fun s => K_norm L s x pix) = (fun s => 1 - (HeatKernel L s) x x / pix) := rfl
  rw [h_K_eq]
  rw [h_sub.deriv]
  ring

--------------------------------------------------------------------------------
-- Helper: Bound on heat kernel diagonal derivative
--------------------------------------------------------------------------------

/-- The derivative of HeatKernel diagonal involves (L * HeatKernel L t)_{xx}. -/
lemma deriv_HeatKernel_diag (L : Matrix V V ℝ) (x : V) (t : ℝ) :
    deriv (fun s => (HeatKernel L s) x x) t = (L * HeatKernel L t) x x := by
  -- The heat kernel satisfies d/dt K(t) = L * K(t)
  -- For the diagonal entry at (x,x), we use heat_semigroup_deriv
  -- Let e_x be the standard basis vector at x
  let e_x : V → ℝ := fun v => if v = x then 1 else 0
  -- (HeatKernel L s) x x = (HeatKernel L s *ᵥ e_x) x
  have h_diag_eq : ∀ s, (HeatKernel L s) x x = (HeatKernel L s *ᵥ e_x) x := by
    intro s
    simp only [mulVec, dotProduct, e_x]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [if_neg hy]
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  -- Similarly for (L * HeatKernel L t) x x
  have h_deriv_eq : (L * HeatKernel L t) x x = (L *ᵥ (HeatKernel L t *ᵥ e_x)) x := by
    simp only [mul_apply, mulVec, dotProduct, e_x]
    congr 1
    ext j
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [if_neg hy]
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  -- Now use the coordinatewise version of heat_semigroup_deriv
  have h_fun_eq : (fun s => (HeatKernel L s) x x) = (fun s => (HeatKernel L s *ᵥ e_x) x) := by
    ext s; exact h_diag_eq s
  rw [h_fun_eq, h_deriv_eq]
  -- deriv (fun s => (HeatKernel L s *ᵥ e_x) x) t = (L *ᵥ (HeatKernel L t *ᵥ e_x)) x
  have h_semigroup := heat_semigroup_deriv L e_x t
  -- Use deriv_pi to go from vector derivative to coordinate derivative
  have h_coord_diff : ∀ v : V, DifferentiableAt ℝ (fun s => (HeatKernel L s *ᵥ e_x) v) t :=
    fun v => HeatKernel_coord_differentiable L e_x v t
  have h_pi := deriv_pi h_coord_diff
  rw [← congr_fun h_pi x, h_semigroup]

--------------------------------------------------------------------------------
-- The Main Theorem
--------------------------------------------------------------------------------

/--
**Spectral Stability Bound**

If the system has a spectral gap > 0, the stability flow is bounded by
an exponential envelope determined by the spectral gap.

**Historical Note:** This result was originally called the "Functorial Heat 
Dominance Theorem (FHDT)" in earlier versions of this library.
-/
theorem spectral_stability_bound
  [Nontrivial V]
  (h_irred : IrreducibilityAssumptions L H pi_dist)
  (h_gap_pos : SpectralGap_pi pi_dist H > 0)
  (hL1 : toLin' L (fun _ => 1) = 0)
  (hK1 : toLin' (HeatKernel L t) (fun _ => 1) = (fun _ => 1))
  (hH_const : H *ᵥ constant_vec_one = 0)
  (h_sa : ∀ u v, inner_pi pi_dist (H *ᵥ u) v = inner_pi pi_dist u (H *ᵥ v))
  (h_psd : ∀ u, 0 ≤ inner_pi pi_dist (H *ᵥ u) u)
  (h_rel : ∀ u v, inner_pi pi_dist (L *ᵥ u) v + inner_pi pi_dist u (L *ᵥ v) = -2 * inner_pi pi_dist (H *ᵥ u) v)
  (h_pos' : ∀ x t, K_norm L t x (pi_dist x) + ε > 0)
  (h_eps_min : ∃ ε_min > 0, ∀ x t, K_norm L t x (pi_dist x) + ε ≥ ε_min)
  -- Additional hypotheses to ensure compatibility
  (hπ : ∀ x, 0 < pi_dist x)
  (h_sum : ∑ x, pi_dist x = 1)
  (t : ℝ) (ht : 0 ≤ t) :
  ∃ C ≥ 0, |stability_flow L pi_dist ε t| ≤ C * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
  -- ════════════════════════════════════════════════════════════════════════════
  -- Setup: We have positivity of pi_dist directly from hπ
  -- ════════════════════════════════════════════════════════════════════════════
  -- Extract ε_min for denominator bounds
  obtain ⟨ε_min, hε_min_pos, hε_min⟩ := h_eps_min
  -- 
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 1: Bound the derivative of the log-observable
  -- β(t) = deriv expected_log_return_prob t = ∑_x π_x * (1/(K_norm + ε)) * deriv K_norm
  -- ════════════════════════════════════════════════════════════════════════════
  -- 
  -- The key bound: |β(t)| ≤ (1/ε_min) * ∑_x π_x * |deriv K_norm|
  -- The derivative of K_norm involves the heat kernel derivative diagonal
  -- which is bounded by the operator norm of L * HeatKernel L t
  -- 
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 2: Use Pillar 3 (Diagonal Bound)
  -- ∑_x |A_{xx}| ≤ |V| * ‖A‖_{op,π}
  -- Here A = L * HeatKernel L t
  -- ════════════════════════════════════════════════════════════════════════════
  -- 
  -- ════════════════════════════════════════════════════════════════════════════
  -- Step 3: Use submultiplicativity and envelope bound
  -- ‖L * e^{tL}‖_{op,π} ≤ ‖L‖_{op,π} * ‖e^{tL}‖_{op,π}
  -- ‖e^{tL} P_⊥‖_{op,π} ≤ e^{-gap*t} (from sector_envelope_bound_canonical)
  -- ════════════════════════════════════════════════════════════════════════════
  -- 
  -- The constant C combines:
  -- - 1/ε_min (from log derivative bound)
  -- - max_x(1/π_x) (from division by π_x)
  -- - |V| (from diagonal sum bound)
  -- - ‖L‖_{op,π} (from submultiplicativity)
  -- - A factor from the envelope B(t) at t=0, which is B(0)=1
  -- 
  -- For now, we construct a universal bound using these components
  -- ════════════════════════════════════════════════════════════════════════════
  -- 
  -- Define the constant C
  -- Use a simpler approach: just pick an arbitrary element for the lower bound
  -- For nonempty V, we can find a minimum pi value
  haveI : Nonempty V := Nontrivial.to_nonempty
  let pi_min : ℝ := Finset.univ.inf' ⟨Classical.arbitrary V, Finset.mem_univ _⟩ pi_dist
  have hpi_min_pos : 0 < pi_min := by
    -- pi_min is the minimum of positive values, so it's positive
    -- For a finite nonempty set, inf' is achieved at some element
    -- The key is that inf' doesn't depend on which nonemptiness proof we use
    have h_univ_nonempty : Finset.univ.Nonempty := ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    -- Use Finset.exists_mem_eq_inf' which says the inf' equals some element
    obtain ⟨x, _, hx_eq⟩ := Finset.exists_mem_eq_inf' h_univ_nonempty pi_dist
    -- pi_min = univ.inf' _ pi_dist = pi_dist x by hx_eq
    -- But we need to handle the different nonemptiness proofs
    have h_pi_min_eq : pi_min = pi_dist x := by
      simp only [pi_min]
      convert hx_eq using 2
    rw [h_pi_min_eq]
    exact hπ x
  -- 
  -- The bound constant incorporates:
  -- C = |V| / (ε_min * pi_min) * ‖L‖_{op,π}
  -- But since we need ‖L‖_{op,π} which requires building it from opNorm_pi,
  -- we use a simplified existence argument.
  -- 
  -- For this assembly, we use that all the necessary tools are available:
  -- 1. The heat kernel derivative is bounded
  -- 2. The diagonal sum is bounded by operator norm
  -- 3. The operator norm decays exponentially
  -- 
  -- The explicit construction requires:
  let C_base := (Fintype.card V : ℝ) / (ε_min * pi_min)
  let L_opNorm := opNorm_pi pi_dist hπ (toLin' L)
  let C := C_base * L_opNorm + 1  -- +1 ensures C > 0 even if L_opNorm = 0
  -- 
  use C
  constructor
  · -- C ≥ 0
    apply add_nonneg
    · apply mul_nonneg
      · apply div_nonneg
        · exact Nat.cast_nonneg _
        · exact mul_pos hε_min_pos hpi_min_pos |>.le
      · exact opNorm_pi_nonneg pi_dist hπ (toLin' L)
    · linarith
  · -- |stability_flow| ≤ C * exp(-gap * t)
    -- 
    -- ══════════════════════════════════════════════════════════════════════════
    -- The proof uses the following key components (all now proved):
    -- 1. deriv_K_norm, deriv_HeatKernel_diag for derivative formulas
    -- 2. sum_abs_diag_le_card_opNorm (Pillar 3) for diagonal bounds
    -- 3. opNorm_pi_comp for submultiplicativity
    -- 4. sector_envelope_bound_canonical (Pillar 2) for exponential decay
    -- 
    -- The key insight is that L * HeatKernel L t factors through P_ortho_pi
    -- since L kills constants, enabling the use of the sector bound.
    -- ══════════════════════════════════════════════════════════════════════════
    -- 
    -- Step 1: Bound opNorm of L * K(t) using factorization through P_ortho_pi
    have hL1_vec : L *ᵥ constant_vec_one = 0 := by
      have := hL1
      simp only [toLin'_apply, constant_vec_one] at this ⊢
      exact this
    have h_sector := sector_envelope_bound_canonical hπ h_sum L H hL1_vec h_sa h_psd hH_const 
                       h_gap_pos h_rel t ht
    -- 
    -- Step 2: Bound diagonal sum using Pillar 3
    have h_diag_bound : ∑ x, |(L * HeatKernel L t) x x| ≤ 
                        (Fintype.card V : ℝ) * opNorm_pi pi_dist hπ (toLin' (L * HeatKernel L t)) :=
      sum_abs_diag_le_card_opNorm hπ (L * HeatKernel L t)
    -- 
    -- Step 3: Constant bound
    have h_C_bound : (Fintype.card V : ℝ) * L_opNorm / (ε_min * pi_min) ≤ C := by
      have h1 : (Fintype.card V : ℝ) * L_opNorm / (ε_min * pi_min) = C_base * L_opNorm := by
        simp only [C_base]; ring
      rw [h1]; simp only [C]; linarith
    -- 
    -- Step 4: The final bound
    -- The remaining computation connects stability_flow to the diagonal sum via:
    -- - Chain rule for log: deriv log(g) = g'/g
    -- - deriv_K_norm and deriv_HeatKernel_diag
    -- - ε_min lower bound on denominators
    -- - π_min lower bound on weights
    -- 
    -- This yields |stability_flow| ≤ (|V|/ε_min/π_min) * ‖L‖ * exp(-gap*t) ≤ C * exp(-gap*t)
    -- ══════════════════════════════════════════════════════════════════════════
    -- Step 5: Factor L * K(t) through P_ortho_pi and bound opNorm
    -- ══════════════════════════════════════════════════════════════════════════
    -- 
    -- Key: For any f, (L * K(t)) *ᵥ f = (L * K(t)) *ᵥ (P_⊥ f)
    -- because K(t) preserves 1 and L kills 1
    have h_LK_opNorm : opNorm_pi pi_dist hπ (toLin' (L * HeatKernel L t)) ≤ 
                       L_opNorm * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
      -- The operator L * K(t) factors as L ∘ K(t) ∘ P_⊥ on any vector
      -- because L kills constants and K preserves them
      -- 
      -- Key property: K(t) preserves constants (from HeatKernel_preserves_one)
      have hK_preserves := HeatKernel_preserves_one L hL1_vec t
      -- K(t) *ᵥ 1 = 1
      have hK1' : (HeatKernel L t) *ᵥ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := by
        have := hK_preserves
        simp only [constant_vec_one] at this
        exact this
      have hL1' : L *ᵥ (fun _ => (1 : ℝ)) = 0 := by
        have := hL1; simp only [toLin'_apply] at this; exact this
      -- 
      have h_factor : ∀ g : V → ℝ, toLin' (L * HeatKernel L t) g = 
                      (toLin' L ∘ₗ toLin' (HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) g := by
        intro g
        simp only [toLin'_apply, LinearMap.comp_apply]
        -- Expand P_ortho_pi: P_⊥ g = g - ⟨g,1⟩ * 1
        simp only [P_ortho_pi, LinearMap.sub_apply, LinearMap.id_apply,
                   LinearMap.smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk]
        -- Goal: (L * K) *ᵥ g = L *ᵥ (K *ᵥ (g - c•1))
        -- First expand RHS: K *ᵥ (g - c*1) = K *ᵥ g - c * (K *ᵥ 1) = K *ᵥ g - c * 1
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hK1']
        -- Now: L *ᵥ (K *ᵥ g - c * 1) = L *ᵥ (K *ᵥ g) - c * (L *ᵥ 1) = L *ᵥ (K *ᵥ g) - 0
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hL1', smul_zero, sub_zero]
        -- LHS: (L * K) *ᵥ g = L *ᵥ (K *ᵥ g) by Matrix.mulVec_mulVec
        exact (Matrix.mulVec_mulVec g L (HeatKernel L t)).symm
      -- Now use operator equality
      have h_eq_op : toLin' (L * HeatKernel L t) = 
                     toLin' L ∘ₗ toLin' (HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ := by
        apply LinearMap.ext; intro g; exact h_factor g
      rw [h_eq_op]
      -- Use submultiplicativity
      have h_comp := opNorm_pi_comp pi_dist hπ (toLin' L) 
                       (toLin' (HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ)
      calc opNorm_pi pi_dist hπ (toLin' L ∘ₗ (toLin' (HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ))
          ≤ opNorm_pi pi_dist hπ (toLin' L) * 
            opNorm_pi pi_dist hπ (toLin' (HeatKernel L t) ∘ₗ P_ortho_pi pi_dist h_sum hπ) := h_comp
        _ ≤ L_opNorm * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
            apply mul_le_mul_of_nonneg_left h_sector
            exact opNorm_pi_nonneg pi_dist hπ (toLin' L)
    -- 
    -- ══════════════════════════════════════════════════════════════════════════
    -- Step 6: Combine diagonal bound with opNorm bound
    -- ══════════════════════════════════════════════════════════════════════════
    -- 
    have h_diag_exp : ∑ x, |(L * HeatKernel L t) x x| ≤ 
                      (Fintype.card V : ℝ) * L_opNorm * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
      calc ∑ x, |(L * HeatKernel L t) x x| 
          ≤ (Fintype.card V : ℝ) * opNorm_pi pi_dist hπ (toLin' (L * HeatKernel L t)) := h_diag_bound
        _ ≤ (Fintype.card V : ℝ) * (L_opNorm * Real.exp (-(SpectralGap_pi pi_dist H) * t)) := by
            apply mul_le_mul_of_nonneg_left h_LK_opNorm (Nat.cast_nonneg _)
        _ = (Fintype.card V : ℝ) * L_opNorm * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by ring
    -- 
    -- ══════════════════════════════════════════════════════════════════════════
    -- Step 7: Bound |stability_flow| using derivative formula and ε_min, π_min
    -- ══════════════════════════════════════════════════════════════════════════
    -- 
    -- The derivative computation gives:
    -- stability_flow = ∑_x π_x * (deriv K_norm) / (K_norm + ε)
    -- |deriv K_norm| ≤ |(L*K)_{xx}| / π_x
    -- 1/(K_norm + ε) ≤ 1/ε_min
    -- 
    -- After combining and using π_min:
    -- |stability_flow| ≤ (1/(ε_min * π_min)) * ∑_x |(L*K)_{xx}|
    -- 
    have h_pi_min_le : ∀ x, pi_min ≤ pi_dist x := by
      intro x
      simp only [pi_min]
      exact Finset.inf'_le _ (Finset.mem_univ x)
    -- 
    have h_beta_bound : |stability_flow L pi_dist ε t| ≤ 
                        (1 / (ε_min * pi_min)) * ∑ x, |(L * HeatKernel L t) x x| := by
      -- ════════════════════════════════════════════════════════════════════════
      -- Step A: Expand stability_flow as a finite sum using chain rule for log
      -- ════════════════════════════════════════════════════════════════════════
      -- 
      -- stability_flow = deriv (∑_x π_x * log(K_norm + ε)) 
      --        = ∑_x π_x * (deriv K_norm) / (K_norm + ε)
      -- 
      -- Define the summand function for each x
      let F (x : V) (s : ℝ) := pi_dist x * Real.log (K_norm L s x (pi_dist x) + ε)
      -- expected_log_return_prob = ∑_x F x
      have hE_eq : expected_log_return_prob L pi_dist ε = fun s => ∑ x, F x s := by
        ext s; simp only [expected_log_return_prob, F]
      -- Each F x is differentiable
      have hF_diff : ∀ x, Differentiable ℝ (F x) := by
        intro x
        simp only [F]
        apply Differentiable.mul
        · exact differentiable_const _
        · apply Differentiable.log
          · apply Differentiable.add
            · exact K_norm_differentiable L x (pi_dist x) (hπ x)
            · exact differentiable_const _
          · intro s; exact ne_of_gt (h_pos' x s)
      -- stability_flow = deriv (∑_x F x) t = ∑_x deriv (F x) t
      have h_beta_sum : stability_flow L pi_dist ε t = ∑ x, deriv (F x) t := by
        simp only [stability_flow, hE_eq]
        -- The goal is: deriv (fun s => ∑ x, F x s) t = ∑ x, deriv (F x) t
        -- First show the function equals the finset sum of functions
        have h_func_eq : (fun s => ∑ x : V, F x s) = ∑ x : V, F x := by
          ext s; exact (Finset.sum_apply s Finset.univ F).symm
        rw [h_func_eq]
        -- Now use deriv_sum 
        rw [deriv_sum (fun x _ => (hF_diff x).differentiableAt)]
      -- 
      -- ════════════════════════════════════════════════════════════════════════
      -- Step B: Compute deriv (F x) using chain rule for log
      -- ════════════════════════════════════════════════════════════════════════
      -- 
      -- deriv (π_x * log(g)) = π_x * (deriv g) / g
      have h_deriv_F : ∀ x, deriv (F x) t = 
          pi_dist x * deriv (fun s => K_norm L s x (pi_dist x)) t / (K_norm L t x (pi_dist x) + ε) := by
        intro x
        simp only [F]
        -- Chain rule: deriv (c * log g) = c * deriv g / g
        have hg_diff : DifferentiableAt ℝ (fun s => K_norm L s x (pi_dist x) + ε) t := 
          ((K_norm_differentiable L x (pi_dist x) (hπ x)).add (differentiable_const ε)).differentiableAt
        have hg_pos : K_norm L t x (pi_dist x) + ε > 0 := h_pos' x t
        have h_log := Real.hasDerivAt_log (ne_of_gt hg_pos)
        have hg_hasderiv : HasDerivAt (fun s => K_norm L s x (pi_dist x) + ε) 
                            (deriv (fun s => K_norm L s x (pi_dist x)) t + 0) t := by
          apply HasDerivAt.add
          · exact (K_norm_differentiable L x (pi_dist x) (hπ x)).differentiableAt.hasDerivAt
          · exact hasDerivAt_const t ε
        have h_log_comp := HasDerivAt.comp t h_log hg_hasderiv
        simp only [add_zero] at h_log_comp
        have h_mul := hasDerivAt_const t (pi_dist x) |>.mul h_log_comp
        simp only [zero_mul, zero_add] at h_mul
        have := h_mul.deriv
        convert this using 1
        ring
      -- 
      -- ════════════════════════════════════════════════════════════════════════
      -- Step C: Use deriv_K_norm to substitute
      -- ════════════════════════════════════════════════════════════════════════
      -- 
      -- deriv K_norm = -(L*K)_{xx} / π_x
      have h_deriv_K : ∀ x, deriv (fun s => K_norm L s x (pi_dist x)) t = 
                       -(L * HeatKernel L t) x x / (pi_dist x) := by
        intro x
        rw [deriv_K_norm L x (pi_dist x) (hπ x) t, deriv_HeatKernel_diag L x t]
      -- 
      -- So deriv (F x) = π_x * (-(L*K)_{xx} / π_x) / (K_norm + ε)
      --                = -(L*K)_{xx} / (K_norm + ε)
      have h_deriv_F_simp : ∀ x, deriv (F x) t = -(L * HeatKernel L t) x x / (K_norm L t x (pi_dist x) + ε) := by
        intro x
        rw [h_deriv_F x, h_deriv_K x]
        have hπ_ne : pi_dist x ≠ 0 := ne_of_gt (hπ x)
        have hg_ne : K_norm L t x (pi_dist x) + ε ≠ 0 := ne_of_gt (h_pos' x t)
        field_simp [hπ_ne, hg_ne]
      -- 
      -- ════════════════════════════════════════════════════════════════════════
      -- Step D: Take absolute values and bound
      -- ════════════════════════════════════════════════════════════════════════
      -- 
      -- |stability_flow| = |∑_x -(L*K)_{xx} / (K_norm + ε)|
      --          ≤ ∑_x |(L*K)_{xx}| / (K_norm + ε)
      --          ≤ ∑_x |(L*K)_{xx}| / ε_min
      --          = (1/ε_min) * ∑_x |(L*K)_{xx}|
      -- 
      have h_bound_eps : |stability_flow L pi_dist ε t| ≤ (1 / ε_min) * ∑ x, |(L * HeatKernel L t) x x| := by
        rw [h_beta_sum]
        simp_rw [h_deriv_F_simp]
        calc |∑ x, -(L * HeatKernel L t) x x / (K_norm L t x (pi_dist x) + ε)|
            ≤ ∑ x, |-(L * HeatKernel L t) x x / (K_norm L t x (pi_dist x) + ε)| := 
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x, |(L * HeatKernel L t) x x| / (K_norm L t x (pi_dist x) + ε) := by
                congr 1; ext x
                rw [abs_div, abs_neg]
                congr 1
                exact abs_of_pos (h_pos' x t)
          _ ≤ ∑ x, |(L * HeatKernel L t) x x| / ε_min := by
                apply Finset.sum_le_sum
                intro x _
                apply div_le_div_of_nonneg_left (abs_nonneg _) hε_min_pos (hε_min x t)
          _ = (1 / ε_min) * ∑ x, |(L * HeatKernel L t) x x| := by
                rw [one_div, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                rw [div_eq_mul_inv, mul_comm]
      -- 
      -- Now use that (1/ε_min) ≤ (1/(ε_min * pi_min)) since pi_min ≤ 1
      have h_pi_min_le_one : pi_min ≤ 1 := by
        -- pi_min = inf {π_x} and ∑_x π_x = 1
        -- Since all π_x > 0 and sum = 1, each π_x ≤ 1, so inf ≤ 1
        have h_exists := Finset.exists_mem_eq_inf' (⟨Classical.arbitrary V, Finset.mem_univ _⟩ : Finset.univ.Nonempty) pi_dist
        obtain ⟨x, _, hx_eq⟩ := h_exists
        have hpi_sum : ∑ y, pi_dist y = 1 := h_sum
        have hx_le : pi_dist x ≤ 1 := by
          calc pi_dist x ≤ ∑ y, pi_dist y := Finset.single_le_sum (fun y _ => (hπ y).le) (Finset.mem_univ x)
            _ = 1 := hpi_sum
        simp only [pi_min]
        calc Finset.univ.inf' ⟨Classical.arbitrary V, Finset.mem_univ _⟩ pi_dist
            = pi_dist x := by convert hx_eq using 2
          _ ≤ 1 := hx_le
      have h_const_le : 1 / ε_min ≤ 1 / (ε_min * pi_min) := by
        apply one_div_le_one_div_of_le
        · exact mul_pos hε_min_pos hpi_min_pos
        · calc ε_min * pi_min ≤ ε_min * 1 := mul_le_mul_of_nonneg_left h_pi_min_le_one hε_min_pos.le
            _ = ε_min := mul_one _
      -- 
      calc |stability_flow L pi_dist ε t| 
          ≤ (1 / ε_min) * ∑ x, |(L * HeatKernel L t) x x| := h_bound_eps
        _ ≤ (1 / (ε_min * pi_min)) * ∑ x, |(L * HeatKernel L t) x x| := by
            apply mul_le_mul_of_nonneg_right h_const_le
            exact Finset.sum_nonneg (fun x _ => abs_nonneg _)
    -- 
    -- ══════════════════════════════════════════════════════════════════════════
    -- Step 8: Final calculation
    -- ══════════════════════════════════════════════════════════════════════════
    -- 
    calc |stability_flow L pi_dist ε t| 
        ≤ (1 / (ε_min * pi_min)) * ∑ x, |(L * HeatKernel L t) x x| := h_beta_bound
      _ ≤ (1 / (ε_min * pi_min)) * ((Fintype.card V : ℝ) * L_opNorm * 
            Real.exp (-(SpectralGap_pi pi_dist H) * t)) := by
          apply mul_le_mul_of_nonneg_left h_diag_exp
          exact one_div_nonneg.mpr (mul_pos hε_min_pos hpi_min_pos).le
      _ = (Fintype.card V : ℝ) * L_opNorm / (ε_min * pi_min) * 
            Real.exp (-(SpectralGap_pi pi_dist H) * t) := by ring
      _ ≤ C * Real.exp (-(SpectralGap_pi pi_dist H) * t) := by
          apply mul_le_mul_of_nonneg_right h_C_bound (Real.exp_nonneg _)

end SGC.Spectral
