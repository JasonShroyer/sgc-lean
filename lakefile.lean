import Lake
open Lake DSL

package «upat» where
  -- Universal Predictive Assembly Theory
  -- Academic Release

require "mathlib" from git "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

@[default_target]
lean_lib «UPAT» where
  srcDir := "src"
  -- Root: src/UPAT.lean

-- Legacy target (optional, keep if needed for old tests)
lean_lib «FHDT» where
  srcDir := "src"

lean_exe «test» where
  root := `test.Main

