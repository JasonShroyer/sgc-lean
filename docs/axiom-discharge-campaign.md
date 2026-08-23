# Axiom Discharge Campaign

## SOUNDNESS HOLE FOUND AND REPAIRED (2026-08-22)

During the ranked-discharge recon, the adjoint family in
SGC/Axioms/GeometryGeneral.lean was found INCONSISTENT as stated:
adjoint_pi_spec was quantified over ALL pi with no positivity hypothesis,
and for degenerate pi (e.g. (1,0) on Fin 2) no adjoint can satisfy it.
False was mechanically derived (scratch/InconsistencyCheck.lean, now a
tombstone; the derivation compiled and #print axioms confirmed it closed
over the two adjoint axioms plus the classical trio). Until the repair,
ANY file importing GeometryGeneral could in principle prove anything.

REPAIR (same day): adjoint_pi_spec / adjoint_pi_involutive /
adjoint_pi_comp now require (hpi : forall v, 0 < pi_dist v); with hpi the
weighted adjoint D^-1 A* D is a model, so the family is satisfiable.
adjoint_pi (construction) and adjoint_pi_zero remain hypothesis-free
(jointly satisfiable). Call sites threaded: GeometryGeneral (1 lemma),
Bridge/Recovery.lean (4 sites), Bridge/Quantum.lean (5 sites) - all
enclosing theorems already carried hpi. Full build + audit gate green.

LESSON: unused axioms are a liability, but USED-and-FALSE axioms are the
emergency. The campaign now audits remaining axioms for SATISFIABILITY
(degenerate-parameter check), not just usage. Full definitional discharge
of the adjoint family (def + 4 theorems, retiring 5 axioms / ~58 refs) is
the top-ranked next discharge.

## Overnight sweep ledger (2026-08-22, night)

- inner_self_adjoint_real: DISCHARGED as theorem, no hypothesis change
  needed - the concrete adjoint makes it true WITHOUT positivity (self-
  adjointness kills degenerate rows AND columns; new stronger lemma
  isSelfAdjoint_inner_symm proven hypothesis-free). Surface 102 -> 101.
- InformationGeometry/RenormalizationDynamics (20 axioms, 2 sorries):
  ZERO consumers import it (verified by grep over src/). Classification:
  WIP quarantine candidate - not on any central theorem path; propose
  removal from build roots or deletion next session (owner call).
- Bridge/GeometricClosure (15 axioms): CENTRAL (imported by
  CurvatureQuotient); headliners provably do NOT depend on its axioms
  (audit certificates pin exact axiom sets). Next satisfiability-sweep
  target; not rushed tonight.
- Satisfiability pattern to test everywhere: axioms quantified over
  parameters admitting degenerate instances (zero measures, empty types,
  zero matrices) - the adjoint lesson.

# Machine inventory (2026-08-22, pre-pruning)

Total `axiom` declarations under src/: **210**
- Referenced somewhere (must be discharged or defended): **110**
- Never referenced (deletion candidates — pure trusted-surface liability): **100**

## Unused axioms (candidates for deletion, pending Jason review)

### SGC\Axioms\GeometryGeneral.lean
- L86: `adjoint_pi_id`
- L102: `inner_pi_nondegenerate`
- L183: `traceNorm_pi_zero`
- L227: `traceDistance_pi_le_one`
- L241: `fidelity_pi_bounds`
- L246: `fidelity_pi_symm`
- L250: `fidelity_pi_eq_one_iff`
- L256: `fuchs_van_de_graaf`
- L275: `traceDistance_classical_eq_TV`

### SGC\Bridge\CanonicalWavelet.lean
- L606: `commutator_norm_nonneg`

### SGC\Bridge\CoherenceObstruction.lean
- L237: `fuzzy_KL_bound`
- L293: `inverse_bridge_topological`
- L307: `toric_code_spectral_gap`
- L334: `classify_code`

### SGC\Bridge\Consolidation.lean
- L264: `InformationLoss_nonneg`
- L273: `defect_bounds_info_loss_rate`

### SGC\Bridge\GeometricClosure.lean
- L210: `spectral_gap_from_ricci`
- L334: `geometric_uncertainty_principle`
- L451: `Gamma_eq_DirichletForm`
- L457: `Gamma_nonneg`
- L518: `DirichletForm_deriv_eq_Gamma2`
- L754: `RelativeEntropy_bounded_by_ChiSquared`
- L847: `Gamma_tensorProduct_additivity`
- L872: `Gamma2_tensorProduct_additivity`

### SGC\Bridge\Quantum.lean
- L142: `embedClassical_isDensityMatrix`
- L833: `approximate_qec_bound`
- L855: `quantum_validity_horizon_bound`

### SGC\Bridge\Recovery.lean
- L139: `RelativeEntropy_eq_zero_iff`
- L199: `ApproximateRecoveryBound`

### SGC\Dynamics\EscortConductance.lean
- L313: `boundary_persistence`

### SGC\Evolution\Conservation.lean
- L63: `betti_zero_components`
- L67: `betti_zero_connected`
- L71: `betti_higher_zero`
- L75: `euler_characteristic`
- L119: `safe_cut_is_safe`
- L123: `safe_cut_removes_stressed`
- L139: `constrained_surgery_is_safe`
- L203: `betti_one_non_increasing`
- L210: `betti_one_sewing`
- L220: `self_preservation`

### SGC\Evolution\Dynamics.lean
- L212: `surgery_step_idempotent_subcritical`
- L243: `trajectory_time_monotone`
- L265: `evolution_entropy_production`
- L284: `equilibrium_is_fixed_point`

### SGC\Evolution\FormanRicci.lean
- L162: `forman_ricci_bottleneck`
- L169: `forman_ricci_cluster`
- L186: `minFormanRicci`
- L191: `maxFormanRicci`

### SGC\Evolution\Surgery.lean
- L106: `sew_preserves_edges`
- L110: `sew_adds_good_edges`

### SGC\Geometry\Conformal.lean
- L115: `corner_angle_pos`
- L119: `corner_angle_lt_pi`
- L123: `triangle_angle_sum`
- L200: `KAT_uniqueness`
- L224: `flatTarget`

### SGC\Geometry\CurvatureBridge.lean
- L92: `ollivier_ricci_exists`

### SGC\Geometry\DiscreteCurvature.lean
- L167: `solidAngle`
- L180: `totalSolidAngle_two`
- L183: `totalSolidAngle_three`
- L335: `yamabe_flow_exists_all_time`
- L366: `yamabe_exponential_convergence`

### SGC\Geometry\Manifold\Convergence.lean
- L256: `spectral_convergence_axiom`

### SGC\Geometry\Simplicial.lean
- L152: `eulerCharacteristic`
- L169: `complexFromGraph`
- L177: `complexFromTriangles`

### SGC\Geometry\Yamabe.lean
- L188: `yamabe_flow_preserves_bound`
- L209: `variance_decreasing`
- L229: `yamabe_convergence`
- L243: `exponential_convergence`
- L277: `consolidation_is_yamabe`

### SGC\InformationGeometry\FisherKL.lean
- L651: `FisherOrthogonalProjector_idempotent`

### SGC\InformationGeometry\InformationGradientLaw.lean
- L309: `chentsov_uniqueness`

### SGC\InformationGeometry\KramersEscape.lean
- L235: `fokker_planck_limit`

### SGC\InformationGeometry\RenormalizationDynamics.lean
- L344: `FisherOperatorNorm_nonneg`
- L383: `FisherSpectralCriterionRel_scale_invariant`
- L656: `spectral_is_variational_optimum`
- L741: `spectral_update_increases_recoverability`
- L770: `update_structure_preserves_criterion`
- L820: `update_metric_psd`
- L879: `intrinsic_defect_lyapunov`
- L899: `intrinsic_defect_exponential_decay`
- L947: `primal_freezing_is_special_case`
- L975: `sgc_closure_principle`
- L1021: `emergence_phase_transition`

### SGC\InformationGeometry\ThermodynamicBridge.lean
- L76: `thermodynamic_uncertainty`
- L104: `jarzynski_equality`
- L113: `crooks_fluctuation`
- L152: `spike_timing_precision`
- L160: `STDP_Fisher_orthogonal`
- L183: `efficient_coding_principle`

### SGC\InformationGeometry\TsallisStatistics.lean
- L237: `TsallisDivergence_eq_zero_iff`
- L452: `escort_entropy_gap_nonneg`

### SGC\Observables\TopologicalPersistence.lean
- L159: `survival_bound`
- L218: `defect_betti_scaling`
- L286: `cycle_exists_from_betti`

### SGC\Renormalization\Approximate.lean
- L965: `NCD_semigroup_bound`

### SGC\Spectral\FloquetTheory.lean
- L142: `floquet_decay_bound`

### SGC\Thermodynamics\EntropyProduction.lean
- L777: `pinsker_inequality`

### SGC\Thermodynamics\Evolution.lean
- L392: `emergence_conjecture`
- L420: `first_law_of_topology`

## Referenced axioms (discharge targets, by usage count)

- `and` (SGC\Bridge\SingularLearning.lean L12) — 1303 reference(s)
- `dimension` (SGC\Geometry\Simplicial.lean L123) — 90 reference(s)
- `partitionToCodeSubspace` (SGC\Bridge\Quantum.lean L148) — 68 reference(s)
- `BettiNumber` (SGC\Evolution\Conservation.lean L60) — 39 reference(s)
- `adjoint_pi` (SGC\Axioms\GeometryGeneral.lean L71) — 38 reference(s)
- `RegularizedFisher` (SGC\InformationGeometry\FisherKL.lean L366) — 21 reference(s)
- `traceNorm_pi` (SGC\Axioms\GeometryGeneral.lean L176) — 14 reference(s)
- `gaspard_path_space_identity` (SGC\Thermodynamics\EntropyProduction.lean L968) — 13 reference(s)
- `StationaryDistribution` (SGC\Thermodynamics\Evolution.lean L115) — 11 reference(s)
- `CommutatorNorm` (SGC\Bridge\CanonicalWavelet.lean L602) — 10 reference(s)
- `YamabeFlow` (SGC\Geometry\Yamabe.lean L181) — 10 reference(s)
- `stationary_is_probability` (SGC\Thermodynamics\Evolution.lean L118) — 10 reference(s)
- `adjoint_pi_spec` (SGC\Axioms\GeometryGeneral.lean L74) — 8 reference(s)
- `TsallisDPI` (SGC\InformationGeometry\TsallisStatistics.lean L281) — 8 reference(s)
- `fidelity_pi` (SGC\Axioms\GeometryGeneral.lean L238) — 7 reference(s)
- `Weyl_inequality_pi` (SGC\Renormalization\Approximate.lean L1093) — 7 reference(s)
- `hidden_entropy_bound_from_trajectory` (SGC\Thermodynamics\EntropyProduction.lean L891) — 7 reference(s)
- `adjoint_pi_comp` (SGC\Axioms\GeometryGeneral.lean L82) — 6 reference(s)
- `geometric_commutator_constraint` (SGC\Bridge\CanonicalWavelet.lean L623) — 6 reference(s)
- `SurgerySew` (SGC\Evolution\Surgery.lean L103) — 6 reference(s)
- `CornerAngle` (SGC\Geometry\Conformal.lean L112) — 6 reference(s)
- `manifold_hypothesis` (SGC\Geometry\Manifold\Convergence.lean L247) — 6 reference(s)
- `FisherOperatorNorm` (SGC\InformationGeometry\RenormalizationDynamics.lean L341) — 6 reference(s)
- `q_persistence_bound` (SGC\InformationGeometry\TsallisStatistics.lean L615) — 6 reference(s)
- `floquet_sgc_bridge` (SGC\Spectral\FloquetTheory.lean L197) — 6 reference(s)
- `mitosis_reduces_structural_free_energy` (SGC\Symbiosis.lean L396) — 5 reference(s)
- `yamabe_bounds_hidden_entropy` (SGC\Geometry\CurvatureBridge.lean L284) — 5 reference(s)
- `score_function` (SGC\InformationGeometry\FisherKL.lean L196) — 5 reference(s)
- `spectral_gap_lower_bounds_defect` (SGC\EmergenceCapacity.lean L215) — 4 reference(s)
- `AnyonRandomWalk` (SGC\Bridge\CoherenceObstruction.lean L281) — 4 reference(s)
- `DataProcessingInequality` (SGC\Bridge\Recovery.lean L156) — 4 reference(s)
- `functional_defect_implies_approx_lumpable` (SGC\Bridge\RennerSGC.lean L136) — 4 reference(s)
- `OllivierRicciCurvature` (SGC\Geometry\CurvatureBridge.lean L89) — 4 reference(s)
- `totalSolidAngle` (SGC\Geometry\DiscreteCurvature.lean L177) — 4 reference(s)
- `KL_Fisher_local_bound` (SGC\InformationGeometry\FisherKL.lean L264) — 4 reference(s)
- `betti_monotone_under_quotient` (SGC\EmergenceCapacity.lean L163) — 3 reference(s)
- `q_poincare_inequality` (SGC\EmergenceCapacity.lean L331) — 3 reference(s)
- `floquet_persistence` (SGC\NonlinearEmergence.lean L203) — 3 reference(s)
- `adjoint_pi_involutive` (SGC\Axioms\GeometryGeneral.lean L78) — 3 reference(s)
- `adjoint_pi_zero` (SGC\Axioms\GeometryGeneral.lean L90) — 3 reference(s)
- `constant_ricci_tight_frame_exists` (SGC\Bridge\CanonicalWavelet.lean L632) — 3 reference(s)
- `defect_bounded_by_ricci` (SGC\Bridge\GeometricClosure.lean L228) — 3 reference(s)
- `Poincare_from_integrated_curvature` (SGC\Bridge\GeometricClosure.lean L540) — 3 reference(s)
- `ConstrainedSurgery` (SGC\Evolution\Conservation.lean L136) — 3 reference(s)
- `diffusionStep` (SGC\Evolution\Dynamics.lean L133) — 3 reference(s)
- `criticalEdges` (SGC\Evolution\Dynamics.lean L187) — 3 reference(s)
- `KAT_existence` (SGC\Geometry\Conformal.lean L193) — 3 reference(s)
- `error_gradient_is_curvature` (SGC\Geometry\CurvatureBridge.lean L323) — 3 reference(s)
- `KAT_existence` (SGC\Geometry\DiscreteCurvature.lean L299) — 3 reference(s)
- `update_structure` (SGC\InformationGeometry\RenormalizationDynamics.lean L765) — 3 reference(s)
- `NCD_defect_split` (SGC\Renormalization\Approximate.lean L942) — 3 reference(s)
- `NCD_integral_bound` (SGC\Renormalization\Approximate.lean L986) — 3 reference(s)
- `floquet_emergence_equivalence` (SGC\NonlinearEmergence.lean L152) — 2 reference(s)
- `linearMap_ext_inner` (SGC\Axioms\GeometryGeneral.lean L107) — 2 reference(s)
- `BakryEmery_implies_stability` (SGC\Bridge\GeometricClosure.lean L185) — 2 reference(s)
- `Ricci_tensor_min` (SGC\Bridge\GeometricClosure.lean L903) — 2 reference(s)
- `partitionToCodeSubspace_proj_eq` (SGC\Bridge\Quantum.lean L153) — 2 reference(s)
- `complexifyDefect_zero_iff` (SGC\Bridge\Quantum.lean L191) — 2 reference(s)
- `KL_coefficient_real` (SGC\Bridge\Quantum.lean L342) — 2 reference(s)
- `PetzRecoveryTheorem` (SGC\Bridge\Recovery.lean L167) — 2 reference(s)
- `SafeSurgeryCut` (SGC\Evolution\Conservation.lean L116) — 2 reference(s)
- `SurgeryStep` (SGC\Evolution\Dynamics.lean L209) — 2 reference(s)
- `discrete_gauss_bonnet` (SGC\Geometry\Conformal.lean L170) — 2 reference(s)
- `discrete_gauss_bonnet` (SGC\Geometry\DiscreteCurvature.lean L215) — 2 reference(s)
- `FisherMatrix_posSemidef` (SGC\InformationGeometry\FisherKL.lean L222) — 2 reference(s)
- `toSubmodule` (SGC\InformationGeometry\RenormalizationDynamics.lean L145) — 2 reference(s)
- `update_metric` (SGC\InformationGeometry\RenormalizationDynamics.lean L818) — 2 reference(s)
- `FiringRateModel` (SGC\InformationGeometry\ThermodynamicBridge.lean L146) — 2 reference(s)
- `defect_bounded_by_assembly` (SGC\Observables\ThermodynamicBounds.lean L92) — 2 reference(s)
- `cycle_induces_blanket` (SGC\Observables\TopologicalPersistence.lean L311) — 2 reference(s)
- `rowsum_to_opNorm_bound` (SGC\Renormalization\Approximate.lean L861) — 2 reference(s)
- `mixing_implies_nonzero_defect` (SGC\EmergenceCapacity.lean L193) — 1 reference(s)
- `inner_self_adjoint_real` (SGC\Axioms\GeometryGeneral.lean L138) — 1 reference(s)
- `traceNorm_pi_nonneg` (SGC\Axioms\GeometryGeneral.lean L179) — 1 reference(s)
- `traceNorm_pi_add` (SGC\Axioms\GeometryGeneral.lean L187) — 1 reference(s)
- `traceNorm_pi_neg` (SGC\Axioms\GeometryGeneral.lean L191) — 1 reference(s)
- `HeatKernel_preserves_nonneg` (SGC\Bridge\CoherenceObstruction.lean L90) — 1 reference(s)
- `HeatKernel_preserves_sum` (SGC\Bridge\CoherenceObstruction.lean L104) — 1 reference(s)
- `norm_zero_forces_alpha_zero` (SGC\Bridge\CoherenceObstruction.lean L159) — 1 reference(s)
- `partition_membership_sum_one` (SGC\Bridge\CoherenceObstruction.lean L216) — 1 reference(s)
- `EnergyDerivative` (SGC\Bridge\GeometricClosure.lean L160) — 1 reference(s)
- `EnergySecondDerivative` (SGC\Bridge\GeometricClosure.lean L163) — 1 reference(s)
- `exponential_decay_from_convexity` (SGC\Bridge\GeometricClosure.lean L199) — 1 reference(s)
- `LandauerPrinciple` (SGC\Bridge\Recovery.lean L254) — 1 reference(s)
- `renner_sgc_bridge_axiom` (SGC\Bridge\RennerSGC.lean L355) — 1 reference(s)
- `rg_monotonicity_of_cheeger` (SGC\Dynamics\EscortConductance.lean L286) — 1 reference(s)
- `diffusionStep_nonneg` (SGC\Evolution\Dynamics.lean L141) — 1 reference(s)
- `diffusionStep_sum` (SGC\Evolution\Dynamics.lean L151) — 1 reference(s)
- `curvature_defect_correspondence` (SGC\Geometry\CurvatureBridge.lean L243) — 1 reference(s)
- `energy_entropy_rate_correspondence` (SGC\Geometry\CurvatureBridge.lean L387) — 1 reference(s)
- `yamabe_flow_convergence` (SGC\Geometry\DiscreteCurvature.lean L352) — 1 reference(s)
- `yamabe_energy_decreasing` (SGC\Geometry\Yamabe.lean L198) — 1 reference(s)
- `score_zero_mean` (SGC\InformationGeometry\FisherKL.lean L200) — 1 reference(s)
- `minimal_disturbance_primal_optimality` (SGC\InformationGeometry\FisherKL.lean L565) — 1 reference(s)
- `fisher_orthogonal_projection_feasibility` (SGC\InformationGeometry\FisherKL.lean L600) — 1 reference(s)
- `fisher_orthogonal_projection_optimality` (SGC\InformationGeometry\FisherKL.lean L613) — 1 reference(s)
- `FisherOrthogonalProjector_orthogonal` (SGC\InformationGeometry\FisherKL.lean L665) — 1 reference(s)
- `no_forgetting_horizon_bound` (SGC\InformationGeometry\FisherKL.lean L777) — 1 reference(s)
- `submodule_dim` (SGC\InformationGeometry\RenormalizationDynamics.lean L150) — 1 reference(s)
- `FisherOperatorNorm_smul` (SGC\InformationGeometry\RenormalizationDynamics.lean L352) — 1 reference(s)
- `spectral_s_update` (SGC\InformationGeometry\RenormalizationDynamics.lean L722) — 1 reference(s)
- `state_fisher_symm` (SGC\InformationGeometry\RenormalizationDynamics.lean L776) — 1 reference(s)
- `state_fisher_psd` (SGC\InformationGeometry\RenormalizationDynamics.lean L780) — 1 reference(s)
- `freeEnergyDiff` (SGC\InformationGeometry\ThermodynamicBridge.lean L94) — 1 reference(s)
- `assembly_bounded_by_defect` (SGC\Observables\ThermodynamicBounds.lean L118) — 1 reference(s)
- `assembly_bounded_by_entropy` (SGC\Observables\ThermodynamicBounds.lean L130) — 1 reference(s)
- `assembly_bounded_by_housekeeping` (SGC\Observables\ThermodynamicBounds.lean L308) — 1 reference(s)
- `laplacian_respects_cycle_blanket` (SGC\Observables\TopologicalPersistence.lean L331) — 1 reference(s)
- `stationary_strictly_positive` (SGC\Thermodynamics\Evolution.lean L263) — 1 reference(s)
- `non_normality_from_flux` (SGC\Thermodynamics\FluxDecomposition.lean L681) — 1 reference(s)