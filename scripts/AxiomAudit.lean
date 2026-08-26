/-
Headline axiom audit — CI gate.

Each `#guard_msgs` block asserts that the named theorem's dependency closure
contains EXACTLY the Lean classical kernel trio and nothing else. If any
project-local axiom, `sorryAx`, or other declaration enters the closure of a
headline theorem, elaboration of this file fails and CI goes red.

Modeling modules elsewhere in the library may declare explicit interface
axioms by design; those are firewalled and audited separately (hygiene
report). This file is the hard gate for the verified core.
-/
import SGC.Topology.PadicPathSpace
import SGC.Bridge.AffinityProtectionQuantitative
import SGC.Bridge.CurvatureUndecidability
import SGC.Bridge.HaltingCompiler
import SGC.Bridge.CantorHalting
import SGC.Geometry.OperatorStrain
import SGC.Bridge.DissipationFloor
import SGC.Topology.BoundaryReadout
import SGC.Renormalization.SymmetryLumpability
import SGC.Renormalization.CurvatureQuotient
import SGC.Thermodynamics.EntropyProduction
import SGC.Bridge.ThreeArrows
import SGC.Renormalization.MeasureReentry
import SGC.Renormalization.KernelHorizon
import SGC.Renormalization.PhysicalHorizon
import SGC.Renormalization.ExpBridge
import SGC.Bridge.TopologicalSensing

/-- info: 'SGC.Topology.PadicPathSpace.pathSpace_homeo_padicInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Topology.PadicPathSpace.pathSpace_homeo_padicInt

/-- info: 'SGC.Topology.PadicPathSpace.pi_pathSpace_homeo_pi_padicInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Topology.PadicPathSpace.pi_pathSpace_homeo_pi_padicInt

/-- info: 'SGC.Bridge.AffinityProtectionQuantitative.killingDefect_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.AffinityProtectionQuantitative.killingDefect_quantitative

/-- info: 'SGC.Bridge.AffinityProtectionQuantitative.killingDefect_exoticLift_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.AffinityProtectionQuantitative.killingDefect_exoticLift_quantitative

/-- info: 'SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.CurvatureUndecidability.cd0_haltW_iff

/-- info: 'SGC.Bridge.CurvatureUndecidability.not_cd0_haltW_of_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.CurvatureUndecidability.not_cd0_haltW_of_halts

/-- info: 'SGC.Bridge.HaltingCompiler.cd0_compiled_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.HaltingCompiler.cd0_compiled_iff

/-- info: 'SGC.Bridge.HaltingCompiler.not_cd0_compiled_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.HaltingCompiler.not_cd0_compiled_iff

/-- info: 'SGC.Bridge.HaltingCompiler.not_cd0_haltNow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.HaltingCompiler.not_cd0_haltNow

/-- info: 'SGC.Bridge.HaltingCompiler.cd0_spinRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.HaltingCompiler.cd0_spinRight

/-- info: 'SGC.Bridge.CantorHalting.resolution_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.CantorHalting.resolution_horizon

/-- info: 'SGC.Bridge.CantorHalting.compiled_gam2_nonneg_away' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.CantorHalting.compiled_gam2_nonneg_away

/-- info: 'SGC.Geometry.OperatorStrain.gam2_strain_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Geometry.OperatorStrain.gam2_strain_eq

/-- info: 'SGC.Geometry.OperatorStrain.driftline_bochner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Geometry.OperatorStrain.driftline_bochner

/-- info: 'SGC.Geometry.OperatorStrain.not_cd0_heavyW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Geometry.OperatorStrain.not_cd0_heavyW

/-- info: 'SGC.Geometry.OperatorStrain.heavyW_dipole_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Geometry.OperatorStrain.heavyW_dipole_sum

/-- info: 'SGC.Bridge.DissipationFloor.entropyProductionRate_ge_killingDefect_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.DissipationFloor.entropyProductionRate_ge_killingDefect_div

/-- info: 'SGC.Bridge.DissipationFloor.dissipation_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.DissipationFloor.dissipation_floor

/-- info: 'SGC.Bridge.DissipationFloor.entropyProduction_pos_of_affinityCharge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.DissipationFloor.entropyProduction_pos_of_affinityCharge

/-- info: 'SGC.Topology.BoundaryReadout.boundary_readout_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Topology.BoundaryReadout.boundary_readout_bound

/-- info: 'SGC.Topology.BoundaryReadout.readout_strongly_lumpable_of_zero_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Topology.BoundaryReadout.readout_strongly_lumpable_of_zero_gain

/-- info: 'SGC.Topology.BoundaryReadout.boundary_readout_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Topology.BoundaryReadout.boundary_readout_lower_bound

/-- info: 'SGC.Topology.BoundaryReadout.not_stronglyLumpable_of_interior_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Topology.BoundaryReadout.not_stronglyLumpable_of_interior_gain

/-- info: 'SGC.Renormalization.SymmetryLumpability.orbitPartition_stronglyLumpable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.SymmetryLumpability.orbitPartition_stronglyLumpable

/-- info: 'SGC.Renormalization.SymmetryLumpability.counterexample_lumpable_not_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.SymmetryLumpability.counterexample_lumpable_not_symmetric

/-- info: 'SGC.Bridge.TopologicalSensing.windingSum_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.TopologicalSensing.windingSum_exact

/-- info: 'SGC.Bridge.TopologicalSensing.flux_eq_zero_of_detailedBalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.TopologicalSensing.flux_eq_zero_of_detailedBalance

/-- info: 'SGC.Bridge.TopologicalSensing.flux_sq_le_killingDefect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.TopologicalSensing.flux_sq_le_killingDefect

/-- info: 'SGC.Bridge.TopologicalSensing.expectedWinding_eq_time_mul_flux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.TopologicalSensing.expectedWinding_eq_time_mul_flux

/-- info: 'SGC.Axioms.GeometryGeneral.inner_self_adjoint_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Axioms.GeometryGeneral.inner_self_adjoint_real

/-- info: 'SGC.Axioms.GeometryGeneral.isSelfAdjoint_inner_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Axioms.GeometryGeneral.isSelfAdjoint_inner_symm

/-- info: 'SGC.Renormalization.KernelHorizon.commutator_columns_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.KernelHorizon.commutator_columns_centered

/-- info: 'SGC.Renormalization.KernelHorizon.kernel_closure_error_le_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.KernelHorizon.kernel_closure_error_le_uniform

/-- info: 'SGC.Renormalization.ExpBridge.exp_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.ExpBridge.exp_intertwine

/-- info: 'SGC.Renormalization.ExpBridge.exp_closure_of_zero_commutator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.ExpBridge.exp_closure_of_zero_commutator

/-- info: 'SGC.Axioms.GeometryGeneral.adjoint_pi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Axioms.GeometryGeneral.adjoint_pi_spec

/-- info: 'SGC.Axioms.GeometryGeneral.adjoint_pi_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Axioms.GeometryGeneral.adjoint_pi_involutive

/-- info: 'SGC.Axioms.GeometryGeneral.adjoint_pi_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Axioms.GeometryGeneral.adjoint_pi_comp

/-- info: 'SGC.Axioms.GeometryGeneral.linearMap_ext_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Axioms.GeometryGeneral.linearMap_ext_inner

/-- info: 'SGC.Renormalization.PhysicalHorizon.closureCommutator_eulerStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.PhysicalHorizon.closureCommutator_eulerStep

/-- info: 'SGC.Renormalization.PhysicalHorizon.physical_time_closure_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.PhysicalHorizon.physical_time_closure_error

/-- info: 'SGC.Renormalization.PhysicalHorizon.commutator_linfty_le_sqrt_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.PhysicalHorizon.commutator_linfty_le_sqrt_defect

/-- info: 'SGC.Renormalization.PhysicalHorizon.end_to_end_physical_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.PhysicalHorizon.end_to_end_physical_horizon

/-- info: 'SGC.Renormalization.KernelHorizon.kernel_closure_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.KernelHorizon.kernel_closure_error_le

/-- info: 'SGC.Renormalization.KernelHorizon.coarseKernel_isStochastic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.KernelHorizon.coarseKernel_isStochastic

/-- info: 'SGC.Renormalization.KernelHorizon.within_tolerance_of_defect_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.KernelHorizon.within_tolerance_of_defect_small

/-- info: 'SGC.Renormalization.MeasureReentry.defectSq_eq_zero_iff_stronglyLumpable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.MeasureReentry.defectSq_eq_zero_iff_stronglyLumpable

/-- info: 'SGC.Renormalization.MeasureReentry.defectSq_eq_weighted_commutator_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.MeasureReentry.defectSq_eq_weighted_commutator_frobenius

/-- info: 'SGC.Renormalization.MeasureReentry.power_closure_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.MeasureReentry.power_closure_telescoping

/-- info: 'SGC.Renormalization.MeasureReentry.defectSq_Lnl_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.MeasureReentry.defectSq_Lnl_pos

/-- info: 'SGC.Thermodynamics.coarseGenerator_eq_quotientGeneratorSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Thermodynamics.coarseGenerator_eq_quotientGeneratorSimple

/-- info: 'SGC.Bridge.ThreeArrows.three_arrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Bridge.ThreeArrows.three_arrows

/-- info: 'SGC.Thermodynamics.data_processing_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Thermodynamics.data_processing_inequality

/-- info: 'SGC.Thermodynamics.hidden_entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Thermodynamics.hidden_entropy_nonneg

/-- info: 'SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient

/-- info: 'SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding
