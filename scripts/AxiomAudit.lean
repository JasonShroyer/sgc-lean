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
import SGC.Renormalization.CurvatureQuotient

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

/-- info: 'SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.CurvatureQuotient.RicciCurvatureBound_quotient

/-- info: 'SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SGC.Renormalization.CurvatureQuotient.StarExample.curvature_hiding
