import Lake
open Lake DSL

package «sgc» where
  -- SGC: The Spectral Geometry of Consolidation
  -- Formal verification of structural persistence in stochastic systems

require "mathlib" from git "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

@[default_target]
lean_lib «SGC» where
  srcDir := "src"
  -- Root: src/SGC.lean

lean_exe «test» where
  root := `test.Main

