# Retired Axioms Ledger

Bulk pruning of unreferenced project-local axioms (2026-08-22).
Classification: "unreferenced in compiled source" — established by exact-name
cross-reference scan over all of src/ plus post-deletion full build + audit gate.
These declarations were NOT proven false and NOT proven true; they were archived
hypotheses/interfaces removed from the active trusted surface. Restoration path:
git history of this file and of the source files (commit noted in git log).

## SGC\Axioms\GeometryGeneral.lean

### `traceDistance_classical_eq_TV` (was L275)
```lean
/-- For classical (diagonal) density matrices, trace distance equals total variation.
    This is the key bridge lemma connecting quantum and classical information theory. -/
axiom traceDistance_classical_eq_TV (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ_dm : IsDensityMatrix pi_dist ρ) (hσ_dm : IsDensityMatrix pi_dist σ)
    (hρ_cl : IsClassical_pi pi_dist ρ) (hσ_cl : IsClassical_pi pi_dist σ) :
    traceDistance_pi pi_dist ρ σ =
      (1/2) * ∑ x, |RCLike.re (ρ (fun y => if y = x then 1 else 0) x) -
                   RCLike.re (σ (fun y => if y = x then 1 else 0) x)|
```

### `fuchs_van_de_graaf` (was L256)
```lean
/-- Fuchs-van de Graaf inequality: relates trace distance and fidelity.
    1 - √F(ρ,σ) ≤ D(ρ,σ) ≤ √(1 - F(ρ,σ)) -/
axiom fuchs_van_de_graaf (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    1 - Real.sqrt (fidelity_pi pi_dist ρ σ) ≤ traceDistance_pi pi_dist ρ σ ∧
    traceDistance_pi pi_dist ρ σ ≤ Real.sqrt (1 - fidelity_pi pi_dist ρ σ)
```

### `fidelity_pi_eq_one_iff` (was L250)
```lean
/-- Fidelity equals 1 iff the states are equal. -/
axiom fidelity_pi_eq_one_iff (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    fidelity_pi pi_dist ρ σ = 1 ↔ ρ = σ
```

### `fidelity_pi_symm` (was L246)
```lean
/-- Fidelity is symmetric. -/
axiom fidelity_pi_symm (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) :
    fidelity_pi pi_dist ρ σ = fidelity_pi pi_dist σ ρ
```

### `fidelity_pi_bounds` (was L241)
```lean
/-- Fidelity is between 0 and 1 for density matrices. -/
axiom fidelity_pi_bounds (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    0 ≤ fidelity_pi pi_dist ρ σ ∧ fidelity_pi pi_dist ρ σ ≤ 1
```

### `traceDistance_pi_le_one` (was L227)
```lean
/-- Trace distance is bounded by 1 for density matrices. -/
axiom traceDistance_pi_le_one (pi_dist : V → ℝ) (ρ σ : (V → 𝕜) →ₗ[𝕜] (V → 𝕜))
    (hρ : IsDensityMatrix pi_dist ρ) (hσ : IsDensityMatrix pi_dist σ) :
    traceDistance_pi pi_dist ρ σ ≤ 1
```

### `traceNorm_pi_zero` (was L183)
```lean
/-- Trace norm of zero is zero. -/
axiom traceNorm_pi_zero (pi_dist : V → ℝ) :
    traceNorm_pi pi_dist (0 : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) = 0
```

### `inner_pi_nondegenerate` (was L102)
```lean
/-- The weighted inner product is non-degenerate: if ⟨x, y⟩ = 0 for all y, then x = 0.
    This holds when all weights π(v) > 0. -/
axiom inner_pi_nondegenerate (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) (x : V → 𝕜) :
    (∀ y, inner_pi pi_dist x y = 0) → x = 0
```

### `adjoint_pi_id` (was L86)
```lean
/-- The adjoint of the identity is the identity. -/
axiom adjoint_pi_id (pi_dist : V → ℝ) :
    adjoint_pi pi_dist (LinearMap.id : (V → 𝕜) →ₗ[𝕜] (V → 𝕜)) = LinearMap.id
```

## SGC\Bridge\CanonicalWavelet.lean

### `commutator_norm_nonneg` (was L606)
```lean
/-- The commutator norm is non-negative. -/
axiom commutator_norm_nonneg (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (hpi : ∀ v, 0 < pi_dist v) :
    CommutatorNorm L pi_dist hpi ≥ 0
```

## SGC\Bridge\CoherenceObstruction.lean

### `classify_code` (was L334)
```lean
/-- **Open Problem**: Classify a given code into the hierarchy.

    This would be the "grand unification" of classical emergence and quantum error correction. -/
axiom classify_code (pi_dist : V → ℝ) (code : CodeSubspace V pi_dist)
    (errors : ErrorOperators V n) : CodeClassification
```

### `toric_code_spectral_gap` (was L307)
```lean
/-- **Toric Code Specific**: The 2D toric code has anyon spectral gap γ ~ 1/L².

    Combined with the inverse bridge, this gives:
    T_logical ≥ exp(cL) / p

    which is the known exponential protection of the toric code. -/
axiom toric_code_spectral_gap (L : ℕ) (hL : 0 < L) :
    haveI : Nonempty (Fin (L * L)) := ⟨⟨0, Nat.mul_pos hL hL⟩⟩
    ∃ (code : TopologicalCode (Fin (L * L))) (walk : AnyonRandomWalk code),
      walk.spectralGap = 1 / (L : ℝ)^2  -- Diffusive scaling
```

### `inverse_bridge_topological` (was L293)
```lean
/-- **The Inverse Bridge Theorem** (Conjectured):

    For topological codes, there exists a classical Markov chain (the anyon walk)
    such that:
    1. The quantum validity horizon equals the classical mixing time
    2. The error threshold equals the spectral gap
    3. Logical error rate decays exponentially with system size

    This would prove: **Topological quantum codes ARE classical Markov chains.** -/
axiom inverse_bridge_topological (code : TopologicalCode V) :
    ∃ (walk : AnyonRandomWalk code),
      -- The spectral gap bounds the error threshold
      ∀ (noise_rate : ℝ), noise_rate < walk.spectralGap →
        -- Logical error time grows exponentially with protection length
        ∃ (c : ℝ), c > 0 ∧
          True  -- validity_horizon ≥ exp(c * code.protection_length) / noise_rate
```

### `AnyonRandomWalk.spectralGap` (was L281)
```lean
/-- **Spectral Gap of Anyon Walk**: The mixing rate of anyon diffusion.
    Axiomatized to avoid technical issues with DecidableEq propagation. -/
axiom AnyonRandomWalk.spectralGap {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {code : TopologicalCode V} (walk : AnyonRandomWalk code) : ℝ
```

### `fuzzy_KL_bound` (was L237)
```lean
/-- **Conjecture (Fuzzy KL)**: For soft partitions with small fuzziness ε,
    the KL coefficient α is bounded by O(ε).

    This would connect:
    - Approximate classical symmetries
    - Approximate quantum error correction
    - Stability of emergent phenomena under perturbation -/
axiom fuzzy_KL_bound (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : SoftPartition V n) (α : ℂ) :
    -- If "soft KL" holds with coefficient α
    -- then |α| ≤ C · fuzziness(P) for some universal C
    True  -- Placeholder for the precise statement
```

## SGC\Bridge\Consolidation.lean

### `defect_bounds_info_loss_rate` (was L273)
```lean
/-- **Defect Bounds Information Loss Rate** (Schema): Small defect implies
    small information loss per unit time.

    ΔD/Δt ≤ C · ‖D‖ where D is the leakage defect. -/
axiom defect_bounds_info_loss_rate (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : IsApproxLumpable L P pi_dist hπ ε)
    (p q : V → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (t : ℝ) (ht : 0 < t) :
    ∃ C > 0, InformationLoss L t p q / t ≤ C * ε
```

### `InformationLoss_nonneg` (was L264)
```lean
/-- Information loss is non-negative (consequence of DPI). -/
axiom InformationLoss_nonneg (L : Matrix V V ℝ) (t : ℝ) (p q : V → ℝ)
    (hT : IsStochasticChannel (HeatKernel L t))
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    0 ≤ InformationLoss L t p q
```

## SGC\Bridge\GeometricClosure.lean

### `Gamma2_tensorProduct_additivity` (was L872)
```lean
/-- **Γ₂ Additivity on Tensor Products**: The curvature decomposes.

    Γ₂_{A×B}(f⊗g) = Γ₂_A(f) ⊗ g² + f² ⊗ Γ₂_B(g) + 2·Γ_A(f) ⊗ Γ_B(g)

    The cross-term 2·Γ_A(f)⊗Γ_B(g) is always ≥ 0, which is why the
    minimum curvature bound is achieved. -/
axiom Gamma2_tensorProduct_additivity (L_A : Matrix V V ℝ) (L_B : Matrix W W ℝ)
    (f : V → ℝ) (g : W → ℝ) (p : V × W) :
    Gamma2ProductSq L_A L_B (f ⊗ₜ g) p =
    ((Gamma2Sq L_A f) ⊗ₜ (fun w => (g w)^2)) p +
    ((fun v => (f v)^2) ⊗ₜ (Gamma2Sq L_B g)) p +
    2 * GammaSq L_A f p.1 * GammaSq L_B g p.2
```

### `Gamma_tensorProduct_additivity` (was L847)
```lean
/-- **Γ Additivity on Tensor Products**: The fundamental decomposition.

    Γ_{A×B}(f⊗g, f⊗g) = Γ_A(f,f) ⊗ g² + f² ⊗ Γ_B(g,g)

    This shows that the "energy" of a tensor product observable decomposes
    into contributions from each subsystem. -/
axiom Gamma_tensorProduct_additivity (L_A : Matrix V V ℝ) (L_B : Matrix W W ℝ)
    (f : V → ℝ) (g : W → ℝ) (p : V × W) :
    GammaProduct L_A L_B (f ⊗ₜ g) (f ⊗ₜ g) p =
    ((GammaSq L_A f) ⊗ₜ (fun w => (g w)^2)) p + ((fun v => (f v)^2) ⊗ₜ (GammaSq L_B g)) p
```

### `RelativeEntropy_bounded_by_ChiSquared` (was L754)
```lean
/-- **Linear Bridge Lemma**: Entropy is bounded by Variance near equilibrium.

    For p close to π (specifically p = π(1 + εf) with small ε):
    D(p ‖ π) ≤ (1/2) χ²(p ‖ π) + O(ε³)

    **Impact**: Variance decay results imply entropy decay in the linear regime.
    This validates thermodynamic predictions for systems operating
    near their stationary distributions. -/
axiom RelativeEntropy_bounded_by_ChiSquared (p pi_dist : V → ℝ)
    (hπ_pos : ∀ v, 0 < pi_dist v)
    (hp_pos : ∀ v, 0 ≤ p v)
    (hp_sum : ∑ v, p v = 1) :
    (RelativeEntropy p pi_dist).toReal ≤ (1/2) * ChiSquared p pi_dist
```

### `DirichletForm_deriv_eq_Gamma2` (was L518)
```lean
/-- **Bochner Identity** (Key to the proof):
    The derivative of DirichletForm along heat flow equals -2 times the π-weighted Γ₂.

    d/dt DirichletForm(f_t) = -2 Σ_x π(x) Γ₂(f_t)(x)

    This is the "engine" of the Bochner technique. It says that Γ₂ controls
    how fast the Dirichlet form is decreasing.

    **Physical Meaning**: Γ₂ measures the "acceleration" of energy dissipation. -/
axiom DirichletForm_deriv_eq_Gamma2 (L : Matrix V V ℝ) (pi_dist : V → ℝ) (f : V → ℝ)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (hπ_pos : ∀ v, 0 < pi_dist v) :
    -- The derivative of DirichletForm(e^{tL}f) at t=0 equals -2 Gamma2_pi
    deriv (fun t => DirichletForm L pi_dist (Spectral.HeatKernel L t *ᵥ f)) 0 =
    -2 * Gamma2_pi L pi_dist f
```

### `Gamma_nonneg` (was L457)
```lean
/-- **Gamma is non-negative**: Γ(f,f) ≥ 0 pointwise for valid generators. -/
axiom Gamma_nonneg (L : Matrix V V ℝ) (f : V → ℝ) (v : V)
    (hL_valid : ∀ i j, i ≠ j → L i j ≥ 0) :
    Gamma L f f v ≥ 0
```

### `Gamma_eq_DirichletForm` (was L451)
```lean
/-- **Gamma-Dirichlet Connection**: The fundamental identity.

    Σ_x π(x) Γ(f,f)(x) = -⟨f, Lf⟩_π

    For generators with L*π = 0 (detailed balance), the RHS equals DirichletForm(f).

    **Proof Idea**: Expand Γ(f,f) = (1/2)(L(f²) - 2f·Lf), integrate against π,
    use that Σ π(x) (Lf)(x) = 0 for probability-preserving generators.

    **Physical Meaning**: The total "gradient energy" (Gamma) equals the
    energy dissipation rate (Dirichlet form). -/
axiom Gamma_eq_DirichletForm (L : Matrix V V ℝ) (pi_dist : V → ℝ)
    (h_stationary : Matrix.vecMul pi_dist L = 0)
    (hπ_pos : ∀ v, 0 < pi_dist v) (f : V → ℝ) :
    Gamma_pi L pi_dist f = -DirichletForm L pi_dist f
```

### `geometric_uncertainty_principle` (was L334)
```lean
/-- **Geometric Uncertainty Principle**: The precision of the effective theory
    is bounded by the inverse Ricci curvature.

    ‖D‖ · tau_mix ≥ C

    where tau_mix ~ 1/(2*rho) is the mixing time. This is analogous to dx*dp ≥ hbar.

    **Physical Meaning**: You cannot have both a precise coarse-graining (small ‖D‖)
    AND slow dynamics (large tau_mix). The geometry sets a fundamental trade-off. -/
axiom geometric_uncertainty_principle (L : Matrix V V ℝ) (P : Partition V)
    (pi_dist : V → ℝ) (hpi : ∀ v, 0 < pi_dist v)
    (rho : ℝ) (h_rho_pos : rho > 0) (h_rho_bound : RicciCurvatureBound L rho) :
    ∃ C > 0, ∀ tau_mix > 0,
      (tau_mix ≥ 1 / (2 * rho)) →
      opNorm_pi pi_dist hpi (DefectOperator L P pi_dist hpi) * tau_mix ≥ C
```

### `spectral_gap_from_ricci` (was L210)
```lean
/-- **Spectral Gap from Ricci Bound**: Positive Ricci curvature implies
    a positive spectral gap.

    Ric ≥ rho > 0 ⟹ gap ≥ 2*rho

    where gap is the spectral gap of the generator L. -/
axiom spectral_gap_from_ricci (L : Matrix V V ℝ) (rho : ℝ)
    (h_rho_pos : rho > 0) (h_rho_bound : RicciCurvatureBound L rho) :
    ∃ gap > 0, gap ≥ 2 * rho
```

## SGC\Bridge\Quantum.lean

### `quantum_validity_horizon_bound` (was L855)
```lean
/-- **Quantum Validity Horizon Theorem**:
    The validity horizon is bounded in terms of the spectral gap and code quality. -/
axiom quantum_validity_horizon_bound (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (L : Matrix V V ℝ) (P : Partition V) (δ : ℝ) (hδ : 0 < δ) :
    let ε := opNorm_pi pi_dist hπ (DefectOperator L P pi_dist hπ)
    let code := partitionToCodeSubspace pi_dist P
    ε > 0 → ∃ (ℒ : Lindbladian V pi_dist),
      quantumValidityHorizon pi_dist ℒ code δ ≥ δ / ε
```

### `approximate_qec_bound` (was L833)
```lean
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
```

### `embedClassical_isDensityMatrix` (was L142)
```lean
/-- The embedding of a classical state is a valid quantum state. -/
axiom embedClassical_isDensityMatrix (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (s : ClassicalState V) :
    IsDensityMatrix pi_dist (embedClassical pi_dist s)
```

## SGC\Bridge\Recovery.lean

### `ApproximateRecoveryBound` (was L199)
```lean
/-- **Approximate Recovery Bound**: Recovery fidelity is bounded by entropy loss.

    If D(p‖q) - D(Mp‖Mq) = ε (small entropy loss), then the Petz map achieves
    F(ℛ(Mp), p) ≥ 1 - ε.

    This is the classical version of the Fawzi-Renner bound.

    Note: Uses `ENNReal.toReal` for the bound since ε is finite when supports are compatible. -/
axiom ApproximateRecoveryBound (M : Matrix V V ℝ) (p q : V → ℝ)
    (hM_stoch : ∀ y, ∑ x, M y x = 1) (hM_nonneg : ∀ y x, 0 ≤ M y x)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    let ε := (RelativeEntropy p q - RelativeEntropy (applyChannel M p) (applyChannel M q)).toReal
    ∃ (R : Matrix V V ℝ),
      ClassicalFidelity (applyChannel R (applyChannel M p)) p ≥ 1 - 2 * Real.sqrt ε
```

### `RelativeEntropy_eq_zero_iff` (was L139)
```lean
/-- D(p‖q) = 0 implies p = q. -/
axiom RelativeEntropy_eq_zero_iff (p q : V → ℝ)
    (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x) :
    RelativeEntropy p q = 0 ↔ p = q
```

## SGC\Dynamics\EscortConductance.lean

### `boundary_persistence` (was L313)
```lean
/-- **Boundary Persistence Theorem**: If a partition has low conductance at
    scale T, it had low conductance at all earlier scales.

    This follows from RG-Monotonicity: h(t) is non-decreasing, so if
    φ(S,T) is low, φ(S,t) was also low for t < T.

    **Contrapositive**: High conductance at early times can become low
    conductance at late times, but not vice versa.

    **Status**: Axiomatized. Follows from rg_monotonicity_of_cheeger. -/
axiom boundary_persistence {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℝ} [NonExtensiveSystem q]
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hZ : EscortNormalization q p ≠ 0)
    (P : HeatSemigroup V) (Part : StatePartition V)
    (threshold t T : ℝ) (_ht : 0 ≤ t) (_htT : t ≤ T)
    (_h_persist : IsPersistentBoundary q p hZ P Part threshold T) :
    Conductance q p hZ (P.at_scale t) Part ≤
    Conductance q p hZ (P.at_scale T) Part
```

## SGC\Evolution\Conservation.lean

### `self_preservation` (was L220)
```lean
/-- **Self-Preservation Theorem**: Systems with blankets that undergo
    constrained surgery maintain their self-environment distinction.

    This is the topological foundation of the Free Energy Principle:
    systems that persist are those whose evolution preserves b₁ ≥ 1.

    **Axiomatized**: The if-then-else requires decidability of IsSafeSurgery. -/
axiom self_preservation (G : WeightedGraph V) (cutTh sewTh : ℝ)
    (hblanket : HasMarkovBlanket G) :
    HasMarkovBlanket (ConstrainedSurgery G cutTh sewTh)
```

### `betti_one_sewing` (was L210)
```lean
/-- **Second Conservation Law**: Sewing can increase b₁.

    Adding edges can create new cycles (new blankets).
    This is how new organizational levels emerge. -/
axiom betti_one_sewing (G : WeightedGraph V) (threshold : ℝ) :
  BettiNumber G 1 ≤ BettiNumber (SurgerySew G threshold) 1
```

### `betti_one_non_increasing` (was L203)
```lean
/-- **First Conservation Law**: Safe surgery can only decrease b₁.

    You can destroy blankets (merge inside with outside) but
    safe surgery prevents this from happening completely. -/
axiom betti_one_non_increasing (G : WeightedGraph V) (threshold : ℝ) :
  BettiNumber (SurgeryCut G threshold) 1 ≤ BettiNumber G 1
```

### `constrained_surgery_is_safe` (was L139)
```lean
/-- Constrained surgery is safe by construction. -/
axiom constrained_surgery_is_safe (G : WeightedGraph V) (cutTh sewTh : ℝ) :
  IsSafeSurgery G (ConstrainedSurgery G cutTh sewTh) ∨ ConstrainedSurgery G cutTh sewTh = G
```

### `safe_cut_removes_stressed` (was L123)
```lean
/-- Safe cut still removes high-stress non-bridge edges. -/
axiom safe_cut_removes_stressed (G : WeightedGraph V) (threshold : ℝ) :
  ∀ u v, G.adj u v → FormanRicci G u v < threshold →
    -- If removing (u,v) keeps the graph connected, it's removed
    (BettiNumber G 0 = BettiNumber (SurgeryCut G threshold) 0) →
    ¬(SafeSurgeryCut G threshold).adj u v
```

### `safe_cut_is_safe` (was L119)
```lean
/-- Safe cut produces safe surgery. -/
axiom safe_cut_is_safe (G : WeightedGraph V) (threshold : ℝ) :
  IsSafeSurgery G (SafeSurgeryCut G threshold)
```

### `euler_characteristic` (was L75)
```lean
/-- Euler characteristic: χ = b₀ - b₁ + b₂ - ... = V - E for graphs. -/
axiom euler_characteristic (G : WeightedGraph V) :
  (BettiNumber G 0 : ℤ) - (BettiNumber G 1 : ℤ) =
    (Fintype.card V : ℤ) - (edgeCount G : ℤ)
```

### `betti_higher_zero` (was L71)
```lean
/-- Higher Betti numbers are zero for graphs (1-complexes). -/
axiom betti_higher_zero (G : WeightedGraph V) (k : ℕ) (hk : k ≥ 2) :
  BettiNumber G k = 0
```

### `betti_zero_connected` (was L67)
```lean
/-- b₀ = 1 iff graph is connected. -/
axiom betti_zero_connected (G : WeightedGraph V) :
  BettiNumber G 0 = 1 ↔ ∀ u v : V, ∃ path : List V, path.head? = some u ∧ path.getLast? = some v
```

### `betti_zero_components` (was L63)
```lean
/-- b₀ counts connected components. -/
axiom betti_zero_components (G : WeightedGraph V) :
  BettiNumber G 0 ≥ 1
```

## SGC\Evolution\Dynamics.lean

### `equilibrium_is_fixed_point` (was L284)
```lean
/-- Equilibrium is a fixed point of the evolution step. -/
axiom equilibrium_is_fixed_point (s : EvolutionaryState V) (dt : ℝ) (hdt : 0 < dt)
    (heq : IsEvolutionaryEquilibrium s) :
    (EvolutionStep s dt (le_of_lt hdt)).G = s.G ∧
    (EvolutionStep s dt (le_of_lt hdt)).π = StationaryDistribution s.G
```

### `evolution_entropy_production` (was L265)
```lean
/-- **Entropy Production**: Evolution increases entropy (second law).

    This is the thermodynamic consistency condition:
    S(t + dt) ≥ S(t) - (heat dissipated) / T

    **Axiomatized**: Full proof requires detailed balance analysis. -/
axiom evolution_entropy_production (s : EvolutionaryState V) (dt : ℝ) (hdt : 0 ≤ dt) :
  let s' := EvolutionStep s dt hdt
  -- Shannon entropy of the distribution
  let H := fun π => -∑ v : V, π v * Real.log (π v)
  H s'.π ≥ H s.π  -- Entropy doesn't decrease
```

### `trajectory_time_monotone` (was L243)
```lean
/-- Time advances monotonically along trajectory. -/
axiom trajectory_time_monotone (s₀ : EvolutionaryState V) (dt : ℝ) (hdt : 0 ≤ dt) (n : ℕ) :
    (EvolutionTrajectory s₀ dt hdt n).t ≤ (EvolutionTrajectory s₀ dt hdt (n + 1)).t
```

### `surgery_step_idempotent_subcritical` (was L212)
```lean
/-- Surgery is idempotent when subcritical. -/
axiom surgery_step_idempotent_subcritical (s : EvolutionaryState V)
    (hsub : IsSubcritical s.G) :
    SurgeryStep s = s
```

## SGC\Evolution\FormanRicci.lean

### `maxFormanRicci` (was L191)
```lean
/-- Maximum edge curvature (most stable edge).

    **Axiomatized**: Requires Nonempty V for sup'. -/
axiom maxFormanRicci (G : WeightedGraph V) : ℝ
```

### `minFormanRicci` (was L186)
```lean
/-- Minimum edge curvature (most stressed edge).

    **Axiomatized**: Requires Nonempty V for inf'. -/
axiom minFormanRicci (G : WeightedGraph V) : ℝ
```

### `forman_ricci_cluster` (was L169)
```lean
/-- Forman-Ricci identifies clusters: low-degree endpoints → positive curvature.

    **Axiomatized**: The full proof requires careful handling of Nat → ℝ coercions. -/
axiom forman_ricci_cluster (G : WeightedGraph V) (u v : V) (h : G.adj u v)
    (hdeg : G.degree u + G.degree v < 4) :
    FormanRicci G u v > 0
```

### `forman_ricci_bottleneck` (was L162)
```lean
/-- Forman-Ricci identifies bottlenecks: high-degree endpoints → negative curvature.

    **Axiomatized**: The full proof requires careful handling of Nat → ℝ coercions. -/
axiom forman_ricci_bottleneck (G : WeightedGraph V) (u v : V) (h : G.adj u v)
    (hdeg : G.degree u + G.degree v > 4) :
    FormanRicci G u v < 0
```

## SGC\Evolution\Surgery.lean

### `sew_adds_good_edges` (was L110)
```lean
/-- Sew adds edges where curvature would be above threshold. -/
axiom sew_adds_good_edges (G : WeightedGraph V) (threshold : ℝ) :
  ∀ u v, (SurgerySew G threshold).adj u v → ¬G.adj u v →
    FormanRicci (SurgerySew G threshold) u v ≥ threshold
```

### `sew_preserves_edges` (was L106)
```lean
/-- Sew only adds edges, never removes them. -/
axiom sew_preserves_edges (G : WeightedGraph V) (threshold : ℝ) :
  ∀ u v, G.adj u v → (SurgerySew G threshold).adj u v
```

## SGC\Geometry\Conformal.lean

### `flatTarget` (was L224)
```lean
/-- **Flat Target**: Zero curvature everywhere (Euclidean).

    Only achievable if χ = 0 (torus or Klein bottle).

    **Axiomatized**: The Gauss-Bonnet constraint requires χ = 0. -/
axiom flatTarget : TargetCurvature V
```

### `KAT_uniqueness` (was L200)
```lean
/-- **KAT Theorem** (Uniqueness up to Möbius):
    The circle packing is unique up to Möbius transformations.

    **Axiomatized**: Uniqueness follows from rigidity of packings. -/
axiom KAT_uniqueness (T : Triangulation V) (hplanar : IsPlanar T)
    (r₁ r₂ : CirclePacking V) :
  ∃ (a b c d : ℝ), True -- Möbius transformation relating r₁ and r₂
```

### `triangle_angle_sum` (was L123)
```lean
/-- Sum of angles in a triangle equals π. -/
axiom triangle_angle_sum (r : CirclePacking V) (t : PackingTriangle V) :
  CornerAngle r t 0 + CornerAngle r t 1 + CornerAngle r t 2 = Real.pi
```

### `corner_angle_lt_pi` (was L119)
```lean
/-- Corner angles are less than π. -/
axiom corner_angle_lt_pi (r : CirclePacking V) (t : PackingTriangle V) (corner : Fin 3) :
  CornerAngle r t corner < Real.pi
```

### `corner_angle_pos` (was L115)
```lean
/-- Corner angles are positive. -/
axiom corner_angle_pos (r : CirclePacking V) (t : PackingTriangle V) (corner : Fin 3) :
  0 < CornerAngle r t corner
```

## SGC\Geometry\CurvatureBridge.lean

### `ollivier_ricci_exists` (was L92)
```lean
/-- Ollivier-Ricci curvature exists and is bounded for any generator. -/
axiom ollivier_ricci_exists (L : Matrix V V ℝ)
    (hL_gen : ∀ x y, x ≠ y → 0 ≤ L x y) :
    ∀ x y, -2 ≤ OllivierRicciCurvature L x y ∧ OllivierRicciCurvature L x y ≤ 1
```

## SGC\Geometry\DiscreteCurvature.lean

### `yamabe_exponential_convergence` (was L366)
```lean
/-- **Exponential Convergence Rate** (Luo 2004):

    The curvature converges exponentially in geometric scale:
    ‖κ(λ) - κ̄‖ ≤ C·e^{-r·λ}·‖κ(0) - κ̄‖
    where r > 0 depends on the spectral gap of the Laplacian, and λ is geometric time.

    **Note**: λ here is consolidation/learning time, not dynamical time t.

    **Axiomatized**: Follows from the gradient flow structure. -/
axiom yamabe_exponential_convergence {V : Type*} [DecidableEq V] [Fintype V]
    (K : SimplicialComplex V) (g : PLMetric V K) :
    ∃ (C rate : ℝ), C > 0 ∧ rate > 0 ∧ True  -- placeholder for exponential bound
```

### `yamabe_flow_exists_all_time` (was L335)
```lean
/-- **Yamabe Flow Long-Time Existence** (Luo 2004, Theorem 1.1):

    The discrete Yamabe flow exists for all geometric scale λ ∈ [0, ∞).
    Unlike smooth PDE flows, the discrete flow never develops singularities.

    **Note**: λ is geometric/consolidation time, not dynamical time t.

    **Axiomatized**: Luo, "Combinatorial Yamabe Flow on Surfaces" (2004) -/
axiom yamabe_flow_exists_all_time {V : Type*} [DecidableEq V] [Fintype V]
    (K : SimplicialComplex V) (g : PLMetric V K) (u₀ : ConformalFactor V) :
    ∀ scale : ℝ, scale ≥ 0 → ∃ _u_scale : ConformalFactor V, True  -- solution at scale λ
```

### `totalSolidAngle_three` (was L183)
```lean
/-- The total solid angle of a sphere is 4π. -/
axiom totalSolidAngle_three : totalSolidAngle 3 = 4 * π
```

### `totalSolidAngle_two` (was L180)
```lean
/-- The total solid angle of a circle is 2π. -/
axiom totalSolidAngle_two : totalSolidAngle 2 = 2 * π
```

### `solidAngle` (was L167)
```lean
/-- **Solid angle** at vertex v in an n-simplex (generalization of interior angle).

    For a tetrahedron with vertex v and opposite face (a,b,c), the solid angle
    is the area of the spherical triangle on the unit sphere at v.

    We axiomatize this for general n, as the explicit formula is complex. -/
axiom solidAngle {V : Type*} [DecidableEq V] [Fintype V]
    {K : SimplicialComplex V} (g : PLMetric V K) (v : V) (σ : Simplex V)
    (hv : v ∈ σ.vertices) : ℝ
```

## SGC\Geometry\Simplicial.lean

### `complexFromTriangles` (was L177)
```lean
/-- Build a simplicial complex from triangulation data.

    **Axiomatized**: Full construction requires enumerating all faces. -/
axiom complexFromTriangles {V : Type*} [DecidableEq V]
    (triangles : Set (Finset V))
    (h_card : ∀ t ∈ triangles, Finset.card t = 3) : AbstractSimplicialComplex V
```

### `complexFromGraph` (was L169)
```lean
/-- Build a simplicial complex from a graph (1-skeleton).

    Every edge {u,v} becomes a 1-simplex, with vertices as 0-simplices.

    **Axiomatized**: Full construction requires careful face closure. -/
axiom complexFromGraph {V : Type*} [DecidableEq V] [Fintype V]
    (adj : V → V → Prop) [DecidableRel adj]
    (adj_symm : ∀ u v, adj u v → adj v u)
    (adj_irrefl : ∀ v, ¬adj v v) : AbstractSimplicialComplex V
```

### `eulerCharacteristic` (was L152)
```lean
/-- The **Euler characteristic** χ = Σ (-1)^k f_k where f_k = # of k-simplices.

    Structural definition: sum over all simplices σ of (-1)^(dim σ).
    This avoids grouping by dimension while computing the same quantity.

    **Axiomatized**: The computation requires converting the finite set to a Finset,
    which depends on choice. We axiomatize the characteristic directly. -/
axiom eulerCharacteristic [Fintype V] (K : AbstractSimplicialComplex V)
    (hfin : Set.Finite K.simplices) : ℤ
```

## SGC\Geometry\Yamabe.lean

### `consolidation_is_yamabe` (was L277)
```lean
/-- **Consolidation Theorem**: Yamabe flow minimizes prediction error.

    The geometric flow (curvature smoothing) is equivalent to
    the statistical flow (error minimization).

    **Axiomatized**: This is the core SGC correspondence. -/
axiom consolidation_is_yamabe (r₀ : CirclePacking V) (T : Triangulation V)
    (dt K_max : ℝ) (hdt : 0 < dt) (hK_max : 0 < K_max) (h_dt : dt * K_max < 1)
    (h_bound : UniformCurvatureBound r₀ T K_max) (n : ℕ) :
  TotalPredictionError (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound (n + 1)) T ≤
  TotalPredictionError (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound n) T
```

### `exponential_convergence` (was L243)
```lean
/-- **Convergence Rate**: Exponential convergence to equilibrium.

    Var(K_n) ≤ Var(K_0) · e^{-λn}

    where λ depends on the spectral gap of the Laplacian.

    **Axiomatized**: Requires spectral analysis. -/
axiom exponential_convergence (r₀ : CirclePacking V) (T : Triangulation V)
    (dt K_max : ℝ) (hdt : 0 < dt) (hK_max : 0 < K_max) (h_dt : dt * K_max < 1)
    (h_bound : UniformCurvatureBound r₀ T K_max) :
  ∃ rate > 0, ∀ n,
    CurvatureVariance (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound n) T ≤
    CurvatureVariance r₀ T * Real.exp (-rate * n)
```

### `yamabe_convergence` (was L229)
```lean
/-- **Uniformization Conjecture**: The flow converges to constant curvature.

    For closed surfaces, the Yamabe flow converges to a metric of
    constant curvature (determined by the Euler characteristic).

    **Axiomatized**: This is the discrete uniformization theorem. -/
axiom yamabe_convergence (r₀ : CirclePacking V) (T : Triangulation V)
    (dt K_max : ℝ) (hdt : 0 < dt) (hK_max : 0 < K_max) (h_dt : dt * K_max < 1)
    (h_bound : UniformCurvatureBound r₀ T K_max) :
  ∃ r_eq : CirclePacking V, IsYamabeEquilibrium r_eq T ∧
    ∀ eps : ℝ, eps > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      CurvatureVariance (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound n) T < eps
```

### `variance_decreasing` (was L209)
```lean
/-- **Variance Monotonicity**: Curvature variance decreases along the flow.

    Var(K_{n+1}) ≤ Var(K_n)

    **Axiomatized**: Requires detailed computation. -/
axiom variance_decreasing (r₀ : CirclePacking V) (T : Triangulation V)
    (dt K_max : ℝ) (hdt : 0 < dt) (hK_max : 0 < K_max) (h_dt : dt * K_max < 1)
    (h_bound : UniformCurvatureBound r₀ T K_max) (n : ℕ) :
  CurvatureVariance (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound (n + 1)) T ≤
  CurvatureVariance (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound n) T
```

### `yamabe_flow_preserves_bound` (was L188)
```lean
/-- **Flow preserves CFL**: The uniform bound is maintained along the flow.

    **Axiomatized**: Requires showing curvature doesn't blow up. -/
axiom yamabe_flow_preserves_bound (r₀ : CirclePacking V) (T : Triangulation V)
    (dt K_max : ℝ) (hdt : 0 < dt) (hK_max : 0 < K_max) (h_dt : dt * K_max < 1)
    (h_bound : UniformCurvatureBound r₀ T K_max) (n : ℕ) :
  UniformCurvatureBound (YamabeFlow r₀ T dt hdt K_max hK_max h_dt h_bound n) T K_max
```

## SGC\Geometry\Manifold\Convergence.lean

### `spectral_convergence_axiom` (was L256)
```lean
/-- **Spectral Convergence** (Axiom):
    
    Eigenvalues of the graph Laplacian converge: λₖ(Lε) → λₖ(Δ).
    
    This ensures spectral gap estimates transfer between scales.
    
    **Proof Path**: Follows from Mosco convergence via Kuwae-Shioya (2003) -/
axiom spectral_convergence_axiom (d : ℕ) (Δ : LaplaceBeltrami d) (k : ℕ) :
    ∀ δ > 0, ∃ (ε₀ : ℝ) (N₀ : ℕ), ε₀ > 0 ∧ N₀ > 0
```

## SGC\InformationGeometry\FisherKL.lean

### `FisherOrthogonalProjector_idempotent` (was L651)
```lean
/-- **AXIOM: Projector Idempotence**

    The projector P_⊥ is idempotent: P² = P.

    **Proof sketch**: P_⊥² = (I - A)(I - A) = I - 2A + A² where A = F⁻¹Sᵀ Gram⁻¹ S.
    Since A² = F⁻¹Sᵀ Gram⁻¹ (SF⁻¹Sᵀ) Gram⁻¹ S = F⁻¹Sᵀ Gram⁻¹ S = A,
    we have P² = I - 2A + A = I - A = P. -/
axiom FisherOrthogonalProjector_idempotent (RF : RegularizedFisher n)
    (S : ConsolidatedSubspace n k)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (h_F_inv : F_reg_inv * RF.regularized = 1)
    (h_Gram_inv : let S_mat := SubspaceMatrix S
                  Gram_inv * (S_mat * F_reg_inv * S_matᵀ) = 1) :
    let P := FisherOrthogonalProjector RF S F_reg_inv Gram_inv
    P * P = P
```

### `RegularizedFisher.posDef` (was L366)
```lean
/-- **AXIOM: Regularized Fisher is Positive Definite**

    For F positive semidefinite and λ > 0, (F + λI) is positive definite.
    This is standard linear algebra: ⟨v, (F + λI)v⟩ = ⟨v, Fv⟩ + λ‖v‖² > 0 for v ≠ 0.

    **Note**: This could be proven using Mathlib's PosDef theory, but we axiomatize
    it to avoid deep dependencies on matrix positivity infrastructure. -/
axiom RegularizedFisher.posDef (RF : RegularizedFisher n) :
    ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * RF.regularized i j * v j
```

## SGC\InformationGeometry\InformationGradientLaw.lean

### `chentsov_uniqueness` (was L309)
```lean
/-- **Chentsov's Theorem** (Axiom): The Fisher metric is the unique (up to scale)
    Riemannian metric on statistical manifolds that is invariant under
    sufficient statistics.

    This is why the Information Gradient (natural gradient) is geometrically
    privileged: it respects the intrinsic geometry of probability space.

    **Consequence**: Learning systems that follow the information gradient
    will find structural solutions faster than those following only the
    energy gradient. -/
axiom chentsov_uniqueness :
  -- The Fisher metric is the unique invariant metric on statistical manifolds
  True  -- Placeholder for the precise category-theoretic statement
```

## SGC\InformationGeometry\KramersEscape.lean

### `fokker_planck_limit` (was L235)
```lean
/-- **Fokker-Planck Limit**: As the graph becomes dense, the SGC master equation
    converges to the Fokker-Planck equation:

    ∂ρ/∂t = ∇·(∇V ρ) + D∇²ρ

    This is the continuum limit where Kramers theory applies. -/
axiom fokker_planck_limit :
  ∀ (L : LossLandscape V) (D : ℝ),
    -- In the continuum limit, SGC dynamics → Fokker-Planck dynamics
    True  -- Placeholder for the precise statement
```

## SGC\InformationGeometry\RenormalizationDynamics.lean

### `emergence_phase_transition` (was L1021)
```lean
/-- **EmergencePhaseTransition**: The predicted behavior in Python.

    The theory predicts a PHASE TRANSITION in the defect plot:
    1. **Chaotic Phase:** High intrinsic defect, gradient fights against structure
    2. **Critical Point:** Defect drops sharply as structure aligns with dynamics
    3. **Emergent Phase:** Low, stable defect plateau (the "Aha!" moment)

    **Falsification Criterion:** If Fisher-orthogonal updates do NOT produce
    this phase transition (defect remains high or fluctuates wildly), the
    theory is WRONG (or the learning rate is too high). -/
axiom emergence_phase_transition (state₀ : RenormalizedState n k)
    (field : GradientField n)
    (trajectory : ℕ → RenormalizedState n k)
    (h_trajectory : ∀ t, ∃ F_inv Gram_inv eta, trajectory (t + 1) = joint_update (trajectory t) field F_inv Gram_inv eta)
    (h_init : trajectory 0 = state₀)
    (D₀ : ℝ) (h_D₀ : D₀ = IntrinsicDefectAtState state₀ field)
    (h_D₀_high : D₀ > 0.5) :  -- Start in chaotic phase
    -- There exists a time T and threshold eps such that defect drops and stays low
    ∃ T : ℕ, ∃ eps : ℝ, eps < 0.1 ∧ ∀ t ≥ T,
      IntrinsicDefectAtState (trajectory t) field < eps
```

### `sgc_closure_principle` (was L975)
```lean
/-- **SGC Closure Principle**: Structure emerges from defect measurements.

    The "right" consolidated subspace S is the one that:
    1. Captures all high-Fisher directions (certainty)
    2. Is compatible with the gradient field (alignment)
    3. Minimizes intrinsic defect in the limit

    **Formally:** S* = argmin_S lim_{t→∞} D_intrinsic(θ_t, S_t)

    This is the variational characterization of emergent structure.

    **Connection to SGC Coarse-Graining:**
    - SGC: Coarse space = image of projector that minimizes defect operator norm
    - Here: Consolidated subspace = kernel of projector that minimizes intrinsic defect

    The duality (image vs kernel) reflects the complementary perspectives:
    - SGC: "What macro-dynamics are preserved?"
    - Learning: "What directions are frozen?" -/
axiom sgc_closure_principle (state₀ : RenormalizedState n k)
    (field : GradientField n)
    (trajectory : ℕ → RenormalizedState n k)
    (h_trajectory : ∀ t, ∃ F_inv Gram_inv eta, trajectory (t + 1) = joint_update (trajectory t) field F_inv Gram_inv eta)
    (h_init : trajectory 0 = state₀) :
    -- The intrinsic defect converges
    ∃ D_limit : ℝ, ∀ ε > 0, ∃ T, ∀ t ≥ T,
      |IntrinsicDefectAtState (trajectory t) field - D_limit| < ε
```

### `primal_freezing_is_special_case` (was L947)
```lean
/-- **Primal Freezing is a Special Case** (axiomatized for simplicity)

    When O_i(θ) = θ_i (coordinate projection), the observable preservation
    constraint reduces to the primal constraint S Δθ = 0.

    This unifies the primal/dual perspectives: we work with observables (dual),
    and primal freezing is recovered when observables are coordinates. -/
axiom primal_freezing_is_special_case (S : ConsolidatedSubspace n k) (theta dtheta : Fin n → ℝ)
    (h_k_le_n : k ≤ n)
    (h_S_is_coordinates : ∀ i : Fin k, ∀ j : Fin n, S.basis i j = if j.val = i.val then 1 else 0) :
    -- If S represents coordinate projections onto first k coordinates...
    (∀ i : Fin k, S.basis i ⬝ᵥ dtheta = 0) ↔
    -- ...then observable preservation = coordinate freezing
    (∀ i : Fin k, dtheta ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_k_le_n⟩ = 0)
```

### `intrinsic_defect_exponential_decay` (was L899)
```lean
/-- **AXIOM: Intrinsic Defect Exponential Decay**

    Under favorable conditions, intrinsic defect decays exponentially:
      D'_intrinsic ≤ (1 - α) · D_intrinsic + O(η²)

    where α > 0 is the "consolidation rate."

    **Interpretation:**
    - α measures how quickly the system discovers and locks in structure
    - The O(η²) term is unavoidable discretization error
    - For emergence: choose η small enough that decay dominates error -/
axiom intrinsic_defect_exponential_decay (state : RenormalizedState n k)
    (field : GradientField n)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (eta alpha C : ℝ)
    (h_alpha_pos : 0 < alpha) (h_alpha_bound : alpha < 1)
    (h_eta_small : 0 < eta) :
    let state' := joint_update state field F_reg_inv Gram_inv eta
    let D := IntrinsicDefectAtState state field
    let D' := IntrinsicDefectAtState state' field
    D' ≤ (1 - alpha) * D + C * eta^2
```

### `intrinsic_defect_lyapunov` (was L879)
```lean
/-- **AXIOM: Intrinsic Defect Lyapunov Stability**

    The joint update law does not increase intrinsic defect:
      D_intrinsic(θ', S') ≤ D_intrinsic(θ, S)

    **This is the non-tautological emergence criterion.**

    Unlike DefectAtPoint (which measures the projected update), IntrinsicDefect
    measures the RAW gradient field. The theorem says: after the joint update,
    the new gradient field is MORE aligned with the new structure.

    **Mathematical Content:**
    1. The structure S evolves to "capture" high-information directions
    2. The parameters θ evolve to make the gradient more compatible with S
    3. The combined effect is non-increasing intrinsic defect

    **Domain of Validity:**
    - Small learning rate η (thermodynamic limit)
    - Smooth gradient field (no discontinuities)
    - Non-degenerate Fisher matrix (full rank after regularization)

    **Why This Isn't Tautological:**
    - S' ≠ S in general (structure evolves)
    - g(θ') ≠ g(θ) in general (gradient changes)
    - The theorem claims these changes CONSPIRE to reduce defect -/
axiom intrinsic_defect_lyapunov (state : RenormalizedState n k)
    (field : GradientField n)
    (F_reg_inv : Matrix (Fin n) (Fin n) ℝ)
    (Gram_inv : Matrix (Fin k) (Fin k) ℝ)
    (eta : ℝ)
    (h_eta_small : 0 < eta ∧ eta < 1) :
    let state' := joint_update state field F_reg_inv Gram_inv eta
    IntrinsicDefectAtState state' field ≤ IntrinsicDefectAtState state field
```

### `update_metric_psd` (was L820)
```lean
axiom update_metric_psd (θ : Fin n → ℝ) :
    Matrix.PosSemidef (update_metric θ)
```

### `update_structure_preserves_criterion` (was L770)
```lean
/-- **UpdateStructure preserves consolidation**: Directions in S' satisfy the criterion.

    This is the key invariant: we only add "mature" directions to S. -/
axiom update_structure_preserves_criterion (state : RenormalizedState n k)
    (field : GradientField n) (crit : ℝ) :
    ∀ i : Fin k, ConsolidationCriterion state.F ((update_structure state field).basis i) crit
```

### `spectral_update_increases_recoverability` (was L741)
```lean
/-- **THEOREM: Recoverability Increases Under Spectral Update**

    If we update S to the spectral eigenspace, recoverability does not decrease.

    **Intuition:**
    The spectral eigenspace is, by definition, the subspace that captures
    the most Fisher information. Any other S of the same dimension captures less.

    **Proof Sketch:**
    Recoverability = Tr(P_S F P_S) / Tr(F)
    For fixed dimension k, this is maximized when S = top-k eigenspace.
    (This is the Eckart-Young theorem for symmetric matrices.) -/
axiom spectral_update_increases_recoverability (state : RenormalizedState n k)
    (field : GradientField n) (tau_stiff P_crit : ℝ)
    (h_trigger : RenormalizationTrigger state field P_crit)
    (S_new : ConsolidatedSubspace n k)
    (h_spectral : IsSpectrallyOptimal state.F S_new tau_stiff) :
    let state_new : RenormalizedState n k := { state with S := S_new }
    RecoverabilityScore state_new ≥ RecoverabilityScore state
```

### `spectral_is_variational_optimum` (was L656)
```lean
/-- **AXIOM: Spectral Selection Approximates Variational Optimum**

    The spectral thresholding rule (S = top eigenspace of F) is the unique
    solution to the variational problem: max_S { Rigidity(S) - λ·Cost(S) }.

    **Why This Matters:**
    This axiom says that our "spectral S-update" is not arbitrary - it is the
    SOLUTION to a well-posed optimization problem with information-theoretic
    justification (MDL/AIC).

    **Proof Sketch:**
    For symmetric F with eigenvalues λ₁ ≥ ... ≥ λₙ, the contribution of
    including eigenvector vᵢ in S is (λᵢ - λ_cost). This is positive iff
    λᵢ > λ_cost. QED. -/
axiom spectral_is_variational_optimum (F : Matrix (Fin n) (Fin n) ℝ)
    (S : ConsolidatedSubspace n k) (lambda_cost : ℝ)
    (h_F_symm : F.IsSymm)
    (h_spectral : IsSpectrallyOptimal F S lambda_cost) :
    -- S maximizes the variational objective among all k-dimensional subspaces
    ∀ S' : ConsolidatedSubspace n k,
      let state := { θ := fun _ => 0, S := S, F := F, reg := 1, h_reg_pos := one_pos }
      let state' := { θ := fun _ => 0, S := S', F := F, reg := 1, h_reg_pos := one_pos }
      VariationalObjective state lambda_cost ≥ VariationalObjective state' lambda_cost
```

### `FisherSpectralCriterionRel_scale_invariant` (was L383)
```lean
/-- **Scale Invariance Theorem**: Relative criterion is invariant under positive scaling.

    If we scale F → αF for α > 0, the criterion FisherSpectralCriterionRel is unchanged.

    **Note on terminology:** This is SCALE-INVARIANCE, not full Fisher-Rao invariance.
    Fisher-Rao invariance would require invariance under arbitrary reparameterizations
    of the statistical model. What we have here is the weaker (but still useful) property
    that the criterion is invariant to global rescaling of F (a "temperature" rescaling).

    **Proof sketch (why this axiom holds):**
    - RayleighQuotient(αF, v) = α · RayleighQuotient(F, v)  [numerator scales, denominator doesn't]
    - FisherOperatorNorm(αF) = α · FisherOperatorNorm(F)    [by FisherOperatorNorm_smul]
    - Therefore: RQ(αF, v) > τ · ‖αF‖ ↔ α·RQ(F,v) > τ·α·‖F‖ ↔ RQ(F,v) > τ·‖F‖ -/
axiom FisherSpectralCriterionRel_scale_invariant
    (F : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (tau_rel α : ℝ) (h_α : 0 < α) :
    FisherSpectralCriterionRel F v tau_rel ↔ FisherSpectralCriterionRel (α • F) v tau_rel
```

### `FisherOperatorNorm_nonneg` (was L344)
```lean
/-- Operator norm is non-negative for PSD matrices. -/
axiom FisherOperatorNorm_nonneg (F : Matrix (Fin n) (Fin n) ℝ)
    (h_psd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * F i j * v j) :
    0 ≤ FisherOperatorNorm F
```

## SGC\InformationGeometry\ThermodynamicBridge.lean

### `efficient_coding_principle` (was L183)
```lean
/-- **Efficient Coding Principle**: Neural systems maximize mutual information
    subject to metabolic constraints.

    max I(stimulus; response) subject to ⟨firing rate⟩ ≤ r_max

    Solution: Fisher-optimal encoding where F_ii ∝ p(stimulus_i) -/
axiom efficient_coding_principle (P : ParametricFamily n V) (θ : Fin n → ℝ)
    (prior : Fin n → ℝ) (h_prior : ∀ i, 0 < prior i) :
    -- Optimal encoding has Fisher proportional to prior
    True  -- Full statement requires optimization framework
```

### `STDP_Fisher_orthogonal` (was L160)
```lean
/-- **STDP as Fisher-Orthogonal Learning**:
    Spike-timing dependent plasticity (STDP) implements updates that are
    approximately Fisher-orthogonal to consolidated spike patterns.

    The STDP window function W(Δt) corresponds to the score function s(θ, spike). -/
axiom STDP_Fisher_orthogonal {k : ℕ} (θ : Fin n → ℝ)
    (consolidated : ConsolidatedSubspace n k) (Δθ_STDP : Fin n → ℝ) :
    -- STDP updates preserve consolidated patterns approximately
    LearningDefect (FiringRateModel n V) θ consolidated Δθ_STDP ≤
      paramNormSq Δθ_STDP  -- Defect is at most O(‖Δθ‖²)
```

### `spike_timing_precision` (was L152)
```lean
/-- **Spike Timing Precision**: The inverse of timing jitter variance.
    σ_t² ≥ 1/F where F is the Fisher information about timing.

    This is the neural Cramér-Rao bound. -/
axiom spike_timing_precision (θ : Fin n → ℝ) :
    ∃ σ_t : ℝ, σ_t^2 ≥ 1 / (∑ i, ∑ j, (FisherMatrix (FiringRateModel n V) θ) i j)
```

### `crooks_fluctuation` (was L113)
```lean
/-- **Crooks Fluctuation Theorem** connection:
    The ratio of forward/reverse work distributions is exponential in work.

    P_F(W) / P_R(-W) = e^{W - ΔF}

    This is the detailed fluctuation theorem that implies Jarzynski. -/
axiom crooks_fluctuation (P : ParametricFamily n V) (θ Δθ : Fin n → ℝ) (W : ℝ) :
    True  -- Placeholder; full statement requires probability measures
```

### `jarzynski_equality` (was L104)
```lean
/-- **Jarzynski Equality** (finite-dimensional version):

    ⟨e^{-W}⟩ = e^{-ΔF}

    Or equivalently: ⟨W⟩ ≥ ΔF (second law)

    This connects thermodynamic work to free energy via exponential averaging.
    The equality holds for any driving protocol, not just quasi-static. -/
axiom jarzynski_equality (P : ParametricFamily n V) (θ Δθ : Fin n → ℝ) :
    thermodynamicWork P θ Δθ ≥ freeEnergyDiff P θ Δθ
```

### `thermodynamic_uncertainty` (was L76)
```lean
/-- **Thermodynamic Uncertainty Relation**:
    The product of thermodynamic length and time bounds the entropy production.

    L² · τ ≥ ΔS_irr

    This is a consequence of the Cramér-Rao bound applied to thermodynamics. -/
axiom thermodynamic_uncertainty (P : ParametricFamily n V)
    (γ : ℝ → (Fin n → ℝ)) (γ' : ℝ → (Fin n → ℝ)) (τ : ℝ) (hτ : 0 < τ)
    (ΔS_irr : ℝ) :
    (ThermodynamicLength P γ γ')^2 * τ ≥ ΔS_irr
```

## SGC\InformationGeometry\TsallisStatistics.lean

### `escort_entropy_gap_nonneg` (was L452)
```lean
/-- **Escort Entropy Gap is Non-Negative**: Irr_q(p) ≥ 0.

    The escort map p ↦ P_q(p) is a deterministic channel (stochastic map).
    By the Tsallis Data Processing Inequality (TsallisDPI), applying a
    stochastic map cannot increase divergence from any reference.

    In particular, the escort concentrates probability, which reduces entropy:
    S_q(P_q(p)) ≤ S_q(p) for q > 1 (the escort emphasizes high-probability states).

    Therefore EscortEntropyGap = S_q(p) - S_q(P_q) ≥ 0.

    For q = 1, P_q = p and the gap is exactly 0 (no irreversibility).
    For q > 1, the gap measures how much the escort concentrates —
    this IS the irreversibility of the nonlinear dynamics. -/
axiom escort_entropy_gap_nonneg {q : ℝ} [NonExtensiveSystem q]
    (p : V → ℝ) (hp_pos : ∀ v, 0 < p v) (hp_sum : ∑ v, p v = 1)
    (hZ : EscortNormalization q p ≠ 0) :
    0 ≤ EscortEntropyGap q p hZ
```

### `TsallisDivergence_eq_zero_iff` (was L237)
```lean
/-- Tsallis divergence is zero iff p = ref.

    **Status**: Axiomatized. The proof requires:
    1. D_q = 0 iff numerator = 0 (since q ≠ 1)
    2. Numerator = 0 iff Σ p^(2-q)·ref^(q-1) = 1
    3. By Young's equality condition, this holds iff p = ref pointwise

    This is a standard characterization of divergence equality. -/
axiom TsallisDivergence_eq_zero_iff {V : Type*} [Fintype V] {q : ℝ} (hq : q ≠ 1)
    (p ref : V → ℝ) (hp_pos : ∀ v, 0 < p v) (href_pos : ∀ v, 0 < ref v)
    (hp_sum : ∑ v, p v = 1) (href_sum : ∑ v, ref v = 1) :
    TsallisDivergence q p ref = 0 ↔ p = ref
```

## SGC\Observables\TopologicalPersistence.lean

### `cycle_exists_from_betti` (was L286)
```lean
/-- **Cycle Existence**: A graph with b₁ ≥ 1 contains at least one cycle.

    This is the fundamental fact from algebraic topology:
    b₁ = dim(H₁) = number of independent cycles.

    For graphs: b₁ = |E| - |V| + b₀ (Euler characteristic).
    b₁ ≥ 1 iff the graph has more edges than a spanning forest. -/
axiom cycle_exists_from_betti (G : WeightedGraph V)
    (hb : HasMarkovBlanket G) :
    ∃ (cycle : List V), cycle.length ≥ 3 ∧
      ∀ i, i + 1 < cycle.length →
        match cycle[i]?, cycle[i+1]? with
        | some u, some v => G.adj u v
        | _, _ => True
```

### `defect_betti_scaling` (was L218)
```lean
/-- **Topological Validity Horizon**: The validity horizon T* relates to persistence.

    For systems where leakage defect ε scales with 1/b₁ (more cycles = better
    self-model), the validity horizon T* = 1/ε scales with b₁.

    This connects topological persistence to predictive validity:
    more robust systems (high b₁) also have longer-valid effective theories. -/
axiom defect_betti_scaling (G : WeightedGraph V) (L : Matrix V V ℝ)
    (P : Partition V) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, C > 0 ∧ ε * (BettiNumber G 1 : ℝ) ≤ C
```

### `survival_bound` (was L159)
```lean
/-- **Survival Theorem**: A system survives k surgery events if b₁ > k.

    This gives a lower bound on the number of destructive events a system
    can withstand while maintaining its Markov blanket.

    Axiomatized: Full proof requires formalization of iterated surgery. -/
axiom survival_bound (G : WeightedGraph V) (k : ℕ) (hk : BettiNumber G 1 > k) :
    ∃ G' : WeightedGraph V, (∀ _i : Fin k, ∃ G_i : WeightedGraph V, IsCyclePreservingSurgery G_i G') ∧ HasMarkovBlanket G'
```

## SGC\Renormalization\Approximate.lean

### `NCD_semigroup_bound` (was L965)
```lean
/-- **NCD Semigroup Bound**: The fast semigroup has bounded operator norm uniformly in time.
    This follows from L_fast being a generator of a contraction semigroup. -/
axiom NCD_semigroup_bound (L_fast : Matrix V V ℝ) (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    ∃ B : ℝ, B ≥ 1 ∧ ∀ t : ℝ, 0 ≤ t →
      opNorm_pi pi_dist hπ (matrixToLinearMap (HeatKernel L_fast t)) ≤ B
```

## SGC\Spectral\FloquetTheory.lean

### `floquet_decay_bound` (was L142)
```lean
axiom floquet_decay_bound (M : MonodromyOperator V) (γ_F : FloquetGap)
    (pi_dist : V → ℝ) (hπ : ∀ v, 0 < pi_dist v) :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : V → ℝ),
        norm_pi pi_dist (MonodromyPropagator M n f) ≤
        C * Real.exp (-γ_F.gap * (n * M.period)) * norm_pi pi_dist f
```

## SGC\Thermodynamics\EntropyProduction.lean

### `pinsker_inequality` (was L777)
```lean
/-- **Pinsker's Inequality**: KL divergence lower-bounds total variation squared.

    D_KL(p ‖ q) ≥ 2 · TV(p, q)²

    Equivalently: D_KL(p ‖ q) ≥ (1/2) ‖p - q‖₁²

    This is a fundamental inequality in information theory, connecting
    entropy (information) to distance (geometry).

    **Axiomatized**: Standard result (Csiszár-Kullback-Pinsker). -/
axiom pinsker_inequality (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1) :
    2 * (TotalVariation p q)^2 ≤ KLDiv p q
```

## SGC\Thermodynamics\Evolution.lean

### `first_law_of_topology` (was L420)
```lean
/-- **The First Law of Topology**: Energy is conserved across surgery.

    The Engine of Creation - the complete evolutionary cycle:
    1. Thermodynamics drives Flow (L updates)
    2. Flow creates Curvature (geometric stress)
    3. Curvature accumulates Stress
    4. Stress pays for Surgery (when > Cost)
    5. Surgery changes Topology
    6. New Topology resets Thermodynamics

    ΔE_system = ΔE_Yamabe + Q_heat

    The geometric relief (curvature smoothing) pays for the
    entropy cost (information erasure).

    **Axiomatized**: The full proof requires coupling thermodynamic
    and geometric flow equations. -/
axiom first_law_of_topology (G G' : WeightedGraph V) :
  let ΔE_struct := StructuralEnergy G' - StructuralEnergy G
  let ΔE_yamabe := totalFormanRicci G' - totalFormanRicci G
  let Q_heat := SurgeryCost G G'
  ΔE_struct = ΔE_yamabe + Q_heat
```

### `emergence_conjecture` (was L392)
```lean
/-- **The Emergence Conjecture**: Geometric flow accumulates stress.

    As the system evolves via Yamabe/Ricci flow on a fixed topology,
    curvature stress accumulates until it exceeds the information cost
    of breaking bonds. This is when **emergence** happens.

    **Axiomatized**: Full proof requires coupling the flow equations
    to the thermodynamic cost function. -/
axiom emergence_conjecture (G : WeightedGraph V) (t : ℕ) :
  let flow := surgeryFlow G 0 0  -- Trivial surgery (no cutting)
  -- After sufficient time, the system becomes critical
  ∃ T, ∀ t' ≥ T, IsCritical (flow t') ∨ IsSurgeryEquilibrium (flow t') 0 0
```
