import SGC.Topology.PadicPathSpace
import SGC.Renormalization.QuotientGenerator
import SGC.InformationGeometry.DefectDynamics
import SGC.Bridge.DiscreteFluidDynamics
import SGC.ComplexityRelativity
import SGC.Bridge.SingularLearning

/-! Ground-truth axiom audit of the four Part-I "Verified Core" keystones.
    A clean result prints only {propext, Classical.choice, Quot.sound}.
    Any `sorryAx` here FALSIFIES the corresponding "ε = 0 / proven" claim. -/

#print axioms SGC.Topology.PadicPathSpace.pathSpace_homeo_padicInt
#print axioms SGC.Renormalization.DefectNotAntitone.defect_not_antitone_under_refinement
#print axioms SGC.InformationGeometry.DefectDynamics.leakage_invariant_under_projection
#print axioms SGC.InformationGeometry.DefectDynamics.projected_update_zero_defect

-- Newly discharged (2026-06-20): must now be clean of the FisherKL custom axiom.
#print axioms SGC.InformationGeometry.FisherKL.minimal_disturbance_primal_feasibility

-- DiscreteFluidDynamics B-series: NESS ⇔ topological cycle, and Killing Defect.
#print axioms SGC.Bridge.DiscreteFluidDynamics.stationary_iff_current_divergence_free
#print axioms SGC.Bridge.DiscreteFluidDynamics.ness_has_current_cycle
#print axioms SGC.Bridge.DiscreteFluidDynamics.reversible_iff_no_positive_current_cycle
#print axioms SGC.Bridge.DiscreteFluidDynamics.killingDefect_eq_zero_iff_reversible
#print axioms SGC.Bridge.DiscreteFluidDynamics.killingDefect_pos_iff_positive_current_cycle
#print axioms SGC.Bridge.DiscreteFluidDynamics.damped_validity_budget

-- ComplexityRelativity capstones (Artemis claims clean; verifying via the gate).
#print axioms SGC.ComplexityRelativity.complexity_is_relational
#print axioms SGC.ComplexityRelativity.constrained_complexity_is_relational
#print axioms SGC.ComplexityRelativity.reversibility_implies_unique_emergence
#print axioms SGC.Renormalization.optimal_partition_exists
#print axioms SGC.Renormalization.reversible_local_iff_global

-- SGC<->SLT bridge (2026-06-20): must rest ONLY on the two documented physics axioms
-- (hidden_entropy_bound_from_trajectory, gaspard_path_space_identity) + classical core.
-- Any NEW axiom here would mean the bridge smuggled in an unproven assumption.
#print axioms SGC.Bridge.SingularLearning.slt_free_energy_le_defect
#print axioms SGC.Bridge.SingularLearning.defect_le_slt_free_energy
