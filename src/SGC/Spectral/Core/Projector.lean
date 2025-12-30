import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import SGC.Spectral.Core.Assumptions

noncomputable section
open Finset LinearMap Matrix Real ContinuousLinearMap

namespace SGC.Spectral
variable {V : Type*} [Fintype V] [DecidableEq V]

--------------------------------------------------------------------------------
-- 1. Explicit L2 Geometry (No Typeclasses)
--------------------------------------------------------------------------------

/-- The L2(pi) norm. -/
def norm_pi (pi_dist : V → ℝ) (f : V → ℝ) : ℝ :=
  Real.sqrt (norm_sq_pi pi_dist f)

/-- Helper: norm_sq_pi as a sum of weighted squares. -/
lemma norm_sq_pi_eq_sum (pi_dist : V → ℝ) (h : V → ℝ) :
    norm_sq_pi pi_dist h = ∑ v, pi_dist v * (h v)^2 := by
  unfold norm_sq_pi inner_pi
  congr 1
  ext v
  rw [pow_two, mul_assoc]

/-- Helper: If norm_sq_pi is zero and weights are positive, then h is zero pointwise. -/
lemma norm_sq_pi_eq_zero_iff (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (h : V → ℝ) :
    norm_sq_pi pi_dist h = 0 ↔ ∀ v, h v = 0 := by
  constructor
  · intro h_zero v
    rw [norm_sq_pi_eq_sum] at h_zero
    have h_nonneg : ∀ x ∈ univ, 0 ≤ pi_dist x * (h x)^2 := fun x _ => mul_nonneg (le_of_lt (h_pos x)) (sq_nonneg (h x))
    have h_term := Finset.sum_eq_zero_iff_of_nonneg h_nonneg
    have h_eq : pi_dist v * (h v)^2 = 0 := h_term.mp h_zero v (mem_univ v)
    rw [pow_two] at h_eq
    have : h v * h v = 0 := (mul_eq_zero.mp h_eq).resolve_left (ne_of_gt (h_pos v))
    exact mul_self_eq_zero.mp this
  · intro h_zero
    rw [norm_sq_pi_eq_sum]
    apply Finset.sum_eq_zero
    intro v _
    simp [h_zero v]

/-- Helper: norm_sq_pi is always nonnegative. -/
lemma norm_sq_pi_nonneg (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (h : V → ℝ) :
    0 ≤ norm_sq_pi pi_dist h := by
  rw [norm_sq_pi_eq_sum]
  apply sum_nonneg
  intro v _
  apply mul_nonneg (le_of_lt (h_pos v)) (sq_nonneg _)

/-- Helper: discriminant inequality from squares. -/
lemma sqrt_ineq_of_sq_le (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (h : b^2 ≤ a * c) :
    |b| ≤ Real.sqrt a * Real.sqrt c := by
  have : Real.sqrt (b^2) ≤ Real.sqrt (a * c) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs] at this
  rw [Real.sqrt_mul ha] at this
  exact this

/-- Helper: Pointwise quadratic expansion. -/
lemma pointwise_quad (f g : V → ℝ) (t : ℝ) (v : V) :
    (f v + t * g v)^2 = (f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2 := by
  have : (f v + t * g v)^2 = (f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2 := by ring
  simpa [pow_two] using this

/-- Helper: Sum-level quadratic expansion. -/
lemma sum_quad (pi_dist : V → ℝ) (f g : V → ℝ) (t : ℝ) :
    ∑ v, pi_dist v * (f v + t * g v)^2 =
    ∑ v, pi_dist v * (f v)^2 + 2 * t * (∑ v, pi_dist v * (f v * g v)) + t^2 * (∑ v, pi_dist v * (g v)^2) := by
  -- Apply pointwise expansion
  have h1 : ∑ v, pi_dist v * (f v + t * g v)^2 =
            ∑ v, pi_dist v * ((f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2) := by
    congr 1
    ext v
    rw [pointwise_quad]
  
  -- Distribute and split sums
  have h2 : ∑ v, pi_dist v * ((f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2) =
            ∑ v, pi_dist v * (f v)^2 + ∑ v, pi_dist v * (2 * t * (f v * g v)) + ∑ v, pi_dist v * (t^2 * (g v)^2) := by
    simp only [mul_add, sum_add_distrib]
  
  -- Pull out constants
  have h3 : ∑ v, pi_dist v * (2 * t * (f v * g v)) = 2 * t * ∑ v, pi_dist v * (f v * g v) := by
    simp only [mul_assoc, mul_comm (pi_dist _), mul_left_comm, mul_sum]
  
  have h4 : ∑ v, pi_dist v * (t^2 * (g v)^2) = t^2 * ∑ v, pi_dist v * (g v)^2 := by
    simp only [mul_assoc, mul_comm (pi_dist _), mul_left_comm, mul_sum]
  
  calc ∑ v, pi_dist v * (f v + t * g v)^2
      = ∑ v, pi_dist v * ((f v)^2 + 2 * t * (f v * g v) + t^2 * (g v)^2) := h1
    _ = ∑ v, pi_dist v * (f v)^2 + ∑ v, pi_dist v * (2 * t * (f v * g v)) + ∑ v, pi_dist v * (t^2 * (g v)^2) := h2
    _ = ∑ v, pi_dist v * (f v)^2 + 2 * t * ∑ v, pi_dist v * (f v * g v) + t^2 * ∑ v, pi_dist v * (g v)^2 := by
        rw [h3, h4]

/-- Cauchy-Schwarz for L2(pi).
    Proven explicitly using the polynomial discriminant method. -/
lemma cauchy_schwarz_pi (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f g : V → ℝ) :
  |inner_pi pi_dist f g| ≤ norm_pi pi_dist f * norm_pi pi_dist g := by
  -- Define coefficients
  let a := norm_sq_pi pi_dist g
  let b := inner_pi pi_dist f g
  let c := norm_sq_pi pi_dist f
  
  -- Define the quadratic P(t) = ||f + t*g||²
  let P (t : ℝ) := norm_sq_pi pi_dist (fun v => f v + t * g v)
  
  -- Step 1: P(t) ≥ 0 for all t
  have hP_nonneg : ∀ t, 0 ≤ P t := fun t => by
    unfold P
    exact norm_sq_pi_nonneg pi_dist h_pos _
  
  -- Step 2: Expand P(t) = c + 2*t*b + t²*a
  have hP_quad : ∀ t, P t = c + 2 * t * b + t^2 * a := by
    intro t
    unfold P a b c
    
    -- Use norm_sq_pi_eq_sum to convert to sums
    have h_left : norm_sq_pi pi_dist (fun v => f v + t * g v) = 
                  ∑ v, pi_dist v * (f v + t * g v)^2 := 
      norm_sq_pi_eq_sum pi_dist (fun v => f v + t * g v)
    
    have h_c : norm_sq_pi pi_dist f = ∑ v, pi_dist v * (f v)^2 := 
      norm_sq_pi_eq_sum pi_dist f
    
    have h_a : norm_sq_pi pi_dist g = ∑ v, pi_dist v * (g v)^2 := 
      norm_sq_pi_eq_sum pi_dist g
    
    have h_b : inner_pi pi_dist f g = ∑ v, pi_dist v * (f v * g v) := by
      unfold inner_pi
      congr 1
      ext v
      rw [mul_assoc]
    
    -- Use sum_quad to expand the quadratic
    have h_sum := sum_quad pi_dist f g t
    
    -- Chain everything together
    calc norm_sq_pi pi_dist (fun v => f v + t * g v)
        = ∑ v, pi_dist v * (f v + t * g v)^2 := h_left
      _ = ∑ v, pi_dist v * (f v)^2 + 2 * t * (∑ v, pi_dist v * (f v * g v)) + t^2 * (∑ v, pi_dist v * (g v)^2) := h_sum
      _ = norm_sq_pi pi_dist f + 2 * t * inner_pi pi_dist f g + t^2 * norm_sq_pi pi_dist g := by
          rw [← h_c, ← h_b, ← h_a]
  
  -- Step 3: Case analysis
  by_cases ha : a = 0
  · -- Case a = 0: g = 0, so b = 0
    have hg : ∀ v, g v = 0 := (norm_sq_pi_eq_zero_iff pi_dist h_pos g).mp ha
    have hb : b = 0 := by
      unfold b inner_pi
      simp [hg]
    unfold b at hb
    rw [hb, abs_zero]
    apply mul_nonneg <;> exact Real.sqrt_nonneg _
  
  · -- Case a ≠ 0: use discriminant
    have ha_pos : 0 < a := by
      have ha_nn := norm_sq_pi_nonneg pi_dist h_pos g
      unfold a at ha_nn ha ⊢
      exact ha_nn.lt_of_ne (Ne.symm ha)
    
    -- Evaluate P at t = -b/a
    have h_vertex := hP_nonneg (-b / a)
    rw [hP_quad] at h_vertex
    
    -- Simplify to get discriminant inequality
    have h_disc : b^2 ≤ a * c := by
      have h_simp : c + 2 * (-b / a) * b + (-b / a)^2 * a = c - b^2 / a := by
        field_simp
        ring
      rw [h_simp] at h_vertex
      have : b^2 / a ≤ c := by linarith
      calc b^2 = a * (b^2 / a) := by field_simp [ne_of_gt ha_pos]
        _ ≤ a * c := mul_le_mul_of_nonneg_left this (le_of_lt ha_pos)
    
    -- Apply sqrt inequality
    have ha_nn := norm_sq_pi_nonneg pi_dist h_pos g
    have hc_nn := norm_sq_pi_nonneg pi_dist h_pos f
    have h_sqrt := sqrt_ineq_of_sq_le a b c ha_nn hc_nn h_disc
    
    -- Convert to norm_pi
    calc |b| = |inner_pi pi_dist f g| := rfl
      _ ≤ Real.sqrt a * Real.sqrt c := h_sqrt
      _ = Real.sqrt c * Real.sqrt a := mul_comm _ _
      _ = norm_pi pi_dist f * norm_pi pi_dist g := by unfold norm_pi a c; rfl

--------------------------------------------------------------------------------
-- 2. Operator Norm (Direct sInf Definition)
--------------------------------------------------------------------------------

/-- The set of constants bounding ‖A f‖_π / ‖f‖_π.
    This is the defining set for the L²(π) operator norm. -/
def opNorm_set (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : Set ℝ :=
  { c | 0 ≤ c ∧ ∀ f, norm_pi pi_dist (A f) ≤ c * norm_pi pi_dist f }

/-- L²(π) Operator Norm.
    Defined as the infimum of all constants c such that ‖A f‖_π ≤ c ‖f‖_π.
    This is the analytically correct operator norm for the L²(π) Hilbert space. -/
def opNorm_pi (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : ℝ :=
  sInf (opNorm_set pi_dist h_pos A)

-- Helper: Scaling isometry used to prove boundedness via Euclidean transport.
def iso_L2_to_std (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) where
  toFun f v := f v * Real.sqrt (pi_dist v)
  invFun g v := g v / Real.sqrt (pi_dist v)
  left_inv f := by funext v; field_simp [Real.sqrt_ne_zero'.mpr (h_pos v)]
  right_inv g := by funext v; field_simp [Real.sqrt_ne_zero'.mpr (h_pos v)]
  map_add' f g := by ext; simp [add_mul]
  map_smul' r f := by ext; simp [mul_assoc]

/-- The isometry property: norm_sq_pi f = Σ (iso f v)².
    Used to show that the conjugated operator has bounded norm. -/
lemma norm_sq_pi_eq_euclidean (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_sq_pi pi_dist f = ∑ v, (iso_L2_to_std pi_dist h_pos f v)^2 := by
  unfold iso_L2_to_std norm_sq_pi inner_pi
  simp only [LinearEquiv.coe_mk]
  apply Finset.sum_congr rfl
  intro v _
  show pi_dist v * f v * f v = (f v * Real.sqrt (pi_dist v)) ^ 2
  rw [mul_pow, Real.sq_sqrt (le_of_lt (h_pos v))]
  ring

/-- norm_pi expressed in terms of iso. -/
lemma norm_pi_eq_sqrt_sum_sq (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = Real.sqrt (∑ v, (iso_L2_to_std pi_dist h_pos f v)^2) := by
  unfold norm_pi
  rw [norm_sq_pi_eq_euclidean]

/-- Key isometry: norm_pi f equals the EuclideanSpace norm of iso(f). -/
lemma norm_pi_eq_euclidean_norm (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = ‖(WithLp.equiv 2 (V → ℝ)).symm (iso_L2_to_std pi_dist h_pos f)‖ := by
  rw [norm_pi_eq_sqrt_sum_sq pi_dist h_pos]
  -- The EuclideanSpace norm is sqrt(Σ ‖g v‖²) = sqrt(Σ (g v)²) for real values
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  -- Need: (iso f v)^2 = ‖(WithLp.equiv.symm (iso f)) v‖^2
  -- The coercion through WithLp is the identity at data level
  -- .ofLp unwraps, so (WithLp.equiv.symm g).ofLp = g
  rw [Real.norm_eq_abs, sq_abs]
  -- Now just need: (iso f v)^2 = ((WithLp.equiv.symm (iso f)).ofLp v)^2
  -- which is rfl since PiLp.ofLp is just the identity coercion
  rfl

/-- The operator norm set is nonempty.
    Uses Euclidean transport to show that a finite constant exists.
    This is the ONLY place where we appeal to the conjugated operator norm. -/
lemma opNorm_set_nonempty (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) 
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : (opNorm_set pi_dist h_pos A).Nonempty := by
  -- Strategy: Transport to EuclideanSpace, use finite-dim operator norm bound, transport back.
  let iso := iso_L2_to_std pi_dist h_pos
  
  -- Define the EuclideanSpace type and transport map
  -- Note: WithLp.equiv is an equivalence at the data level (same underlying type, different norm)
  let E := EuclideanSpace ℝ V
  let toE : (V → ℝ) → E := (WithLp.equiv 2 (V → ℝ)).symm
  let fromE : E → (V → ℝ) := WithLp.equiv 2 (V → ℝ)
  
  -- The conjugated operator on EuclideanSpace
  -- This is well-defined because iso and A are linear, and WithLp.equiv preserves linearity
  let A_E : E →ₗ[ℝ] E := 
    { toFun := fun g => toE (iso (A (iso.symm (fromE g))))
      map_add' := fun x y => by
        -- WithLp.equiv is an AddEquiv, so it preserves addition
        change toE (iso (A (iso.symm (fromE (x + y))))) = 
               toE (iso (A (iso.symm (fromE x)))) + toE (iso (A (iso.symm (fromE y))))
        -- fromE (x + y) = fromE x + fromE y (definitionally for WithLp)
        have h1 : fromE (x + y) = fromE x + fromE y := rfl
        rw [h1, map_add, map_add, map_add]
        -- toE (a + b) = toE a + toE b (definitionally for WithLp)
        rfl
      map_smul' := fun m x => by
        change toE (iso (A (iso.symm (fromE (m • x))))) = 
               m • toE (iso (A (iso.symm (fromE x))))
        -- fromE (m • x) = m • fromE x (definitionally for WithLp)
        have h1 : fromE (m • x) = m • fromE x := rfl
        rw [h1, map_smul, map_smul, map_smul]
        -- toE (m • a) = m • toE a (definitionally for WithLp)
        rfl }
  
  -- Get the operator norm bound from finite-dimensionality
  let C := ‖A_E.toContinuousLinearMap‖
  
  use C
  refine ⟨norm_nonneg _, ?_⟩
  intro f
  
  -- Show: norm_pi(A f) ≤ C * norm_pi(f)
  have h_Af : norm_pi pi_dist (A f) = ‖toE (iso (A f))‖ := 
    norm_pi_eq_euclidean_norm pi_dist h_pos (A f)
  
  have h_f : norm_pi pi_dist f = ‖toE (iso f)‖ := 
    norm_pi_eq_euclidean_norm pi_dist h_pos f
  
  -- The conjugation identity: toE(iso(A f)) = A_E(toE(iso f))
  have h_conj : toE (iso (A f)) = A_E (toE (iso f)) := by
    simp only [A_E, LinearMap.coe_mk, AddHom.coe_mk, iso, fromE, toE]
    congr 1
    rw [Equiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  
  -- Apply the operator norm bound
  have h_bound : ‖A_E (toE (iso f))‖ ≤ C * ‖toE (iso f)‖ := 
    ContinuousLinearMap.le_opNorm A_E.toContinuousLinearMap (toE (iso f))
  
  calc norm_pi pi_dist (A f) 
      = ‖toE (iso (A f))‖ := h_Af
    _ = ‖A_E (toE (iso f))‖ := by rw [h_conj]
    _ ≤ C * ‖toE (iso f)‖ := h_bound
    _ = C * norm_pi pi_dist f := by rw [h_f]

/-- The operator norm set is bounded below by 0. -/
lemma opNorm_set_bddBelow (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) 
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) : BddBelow (opNorm_set pi_dist h_pos A) :=
  ⟨0, fun _ hc => hc.1⟩

/-- Zero is a lower bound of opNorm_set. -/
lemma opNorm_set_zero_le_mem (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) 
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (c : ℝ) (hc : c ∈ opNorm_set pi_dist h_pos A) : 0 ≤ c :=
  hc.1

/-- Helper: norm_pi f = 0 implies f = 0 (pointwise). -/
lemma norm_pi_eq_zero_iff (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    norm_pi pi_dist f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext v
    have h_sq : norm_sq_pi pi_dist f = 0 := by
      unfold norm_pi at hf
      have := Real.sqrt_eq_zero (norm_sq_pi_nonneg pi_dist h_pos f)
      exact this.mp hf
    exact (norm_sq_pi_eq_zero_iff pi_dist h_pos f).mp h_sq v
  · intro hf
    simp [hf, norm_pi, norm_sq_pi, inner_pi]

/-- Helper: norm_pi is positive for nonzero functions. -/
lemma norm_pi_pos_of_ne_zero (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) 
    (hf : f ≠ 0) : 0 < norm_pi pi_dist f := by
  unfold norm_pi
  apply Real.sqrt_pos_of_pos
  have : norm_sq_pi pi_dist f ≠ 0 := by
    intro h_eq
    exact hf ((norm_sq_pi_eq_zero_iff pi_dist h_pos f).mp h_eq |> funext)
  exact (norm_sq_pi_nonneg pi_dist h_pos f).lt_of_ne' this

/-- **The Bound Lemma.** ‖A f‖_π ≤ ‖A‖_π * ‖f‖_π.
    Follows directly from the sInf definition: opNorm_pi is the greatest lower bound
    of all valid constants, and any such constant satisfies the bound. -/
lemma opNorm_pi_bound (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) 
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (f : V → ℝ) :
    norm_pi pi_dist (A f) ≤ opNorm_pi pi_dist h_pos A * norm_pi pi_dist f := by
  unfold opNorm_pi
  -- Strategy: Every c in opNorm_set satisfies the bound, so sInf also does.
  -- We use that the bound holds for all c in the set, and pass to the limit.
  
  by_cases hf : f = 0
  · -- If f = 0, both sides are 0
    simp [hf, norm_pi, norm_sq_pi, inner_pi]
  · -- f ≠ 0, so norm_pi f > 0
    have hf_pos : 0 < norm_pi pi_dist f := norm_pi_pos_of_ne_zero pi_dist h_pos f hf
    
    -- Key: for all c in opNorm_set, norm_pi(Af) ≤ c * norm_pi(f)
    -- Therefore: norm_pi(Af) / norm_pi(f) ≤ c for all c in opNorm_set
    -- So: norm_pi(Af) / norm_pi(f) ≤ sInf(opNorm_set)
    -- Rearranging: norm_pi(Af) ≤ sInf(opNorm_set) * norm_pi(f)
    
    have h_ratio_le : ∀ c ∈ opNorm_set pi_dist h_pos A, 
        norm_pi pi_dist (A f) / norm_pi pi_dist f ≤ c := by
      intro c hc
      rw [div_le_iff₀ hf_pos]
      exact hc.2 f
    
    have h_ratio_le_sInf : norm_pi pi_dist (A f) / norm_pi pi_dist f ≤ 
        sInf (opNorm_set pi_dist h_pos A) := by
      apply le_csInf (opNorm_set_nonempty pi_dist h_pos A)
      exact h_ratio_le
    
    calc norm_pi pi_dist (A f) 
        = (norm_pi pi_dist (A f) / norm_pi pi_dist f) * norm_pi pi_dist f := by
            field_simp
      _ ≤ sInf (opNorm_set pi_dist h_pos A) * norm_pi pi_dist f := by
            apply mul_le_mul_of_nonneg_right h_ratio_le_sInf (le_of_lt hf_pos)

--------------------------------------------------------------------------------
-- 3. Projector (Standard)
--------------------------------------------------------------------------------
def P_ortho_pi (pi_dist : V → ℝ) (h_sum : ∑ v, pi_dist v = 1) (h_pos : ∀ v, 0 < pi_dist v) :
  (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  let P_inner : (V → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => inner_pi pi_dist f (fun _ => 1)
      map_add' := by intros; simp [inner_pi_add_left]
      map_smul' := by intros; simp [inner_pi_smul_left] }
  LinearMap.id - (LinearMap.smulRight P_inner (fun _ => 1))

-- Required lemmas

/-- The L²(π) operator norm is nonnegative.
    Follows from the sInf definition: all elements of opNorm_set are ≥ 0. -/
lemma opNorm_pi_nonneg (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) :
    0 ≤ opNorm_pi pi_dist h_pos A := by
  unfold opNorm_pi
  apply Real.sInf_nonneg
  intro c hc
  exact hc.1

/-- Submultiplicativity: ‖A ∘ B‖_π ≤ ‖A‖_π * ‖B‖_π.
    Proven via the sInf definition: if c bounds A and d bounds B, then c*d bounds A∘B. -/
lemma opNorm_pi_comp (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) (A B : (V → ℝ) →ₗ[ℝ] (V → ℝ)) :
    opNorm_pi pi_dist h_pos (A ∘ₗ B) ≤ opNorm_pi pi_dist h_pos A * opNorm_pi pi_dist h_pos B := by
  unfold opNorm_pi
  -- Show that ‖A‖_π * ‖B‖_π is in opNorm_set(A∘B), then use sInf ≤ element
  apply csInf_le (opNorm_set_bddBelow pi_dist h_pos (A ∘ₗ B))
  -- Need to show: sInf(A) * sInf(B) ∈ opNorm_set(A∘B)
  constructor
  · -- Nonnegativity
    apply mul_nonneg
    · apply Real.sInf_nonneg; intro c hc; exact hc.1
    · apply Real.sInf_nonneg; intro c hc; exact hc.1
  · -- Bound property: ‖(A∘B)f‖_π ≤ ‖A‖_π * ‖B‖_π * ‖f‖_π
    intro f
    calc norm_pi pi_dist ((A ∘ₗ B) f)
        = norm_pi pi_dist (A (B f)) := rfl
      _ ≤ sInf (opNorm_set pi_dist h_pos A) * norm_pi pi_dist (B f) := by
          have := opNorm_pi_bound pi_dist h_pos A (B f)
          unfold opNorm_pi at this
          exact this
      _ ≤ sInf (opNorm_set pi_dist h_pos A) * (sInf (opNorm_set pi_dist h_pos B) * norm_pi pi_dist f) := by
          apply mul_le_mul_of_nonneg_left
          · have := opNorm_pi_bound pi_dist h_pos B f
            unfold opNorm_pi at this
            exact this
          · apply Real.sInf_nonneg; intro c hc; exact hc.1
      _ = sInf (opNorm_set pi_dist h_pos A) * sInf (opNorm_set pi_dist h_pos B) * norm_pi pi_dist f := by ring

/-- If c ≥ 0 and ‖A f‖_π ≤ c * ‖f‖_π for all f, then ‖A‖_π ≤ c.
    This is the converse direction: from a pointwise bound to an operator norm bound. -/
lemma opNorm_pi_le_of_bound (pi_dist : V → ℝ) (h_pos : ∀ v, 0 < pi_dist v) 
    (A : (V → ℝ) →ₗ[ℝ] (V → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (h_bound : ∀ f, norm_pi pi_dist (A f) ≤ c * norm_pi pi_dist f) :
    opNorm_pi pi_dist h_pos A ≤ c := by
  unfold opNorm_pi
  -- c ∈ opNorm_set, so sInf ≤ c
  apply csInf_le (opNorm_set_bddBelow pi_dist h_pos A)
  exact ⟨hc, h_bound⟩

end SGC.Spectral
