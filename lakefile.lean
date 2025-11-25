import Lake
open Lake DSL

package «fhdt» where
  -- Add package configuration here

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

@[default_target]
lean_lib «FHDT» where
  srcDir := "src"

lean_exe «test» where
  root := `test.Main
  