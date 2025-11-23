import Lake
open Lake DSL

package «fhdt» where
  -- Add package configuration here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5f55e56e12e10c5678a2e1d1f04f6c498a87f167"

@[default_target]
lean_lib «FHDT» where
  -- Add library configuration here

lean_exe «test» where
  root := `test.Main
