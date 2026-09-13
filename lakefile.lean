import Lake
open Lake DSL

package «sgc» where
  -- SGC: The Spectral Geometry of Consolidation
  -- Two Horizons: coarse-graining defects, fluid computation, regularity budgets

require "mathlib" from git "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

@[default_target]
lean_lib «SGC» where
  srcDir := "src"
  -- Root: src/SGC.lean
