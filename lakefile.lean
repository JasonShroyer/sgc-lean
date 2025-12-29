import Lake
open Lake DSL

package «upat» where
  -- UPAT: The Spectral Geometry of Consolidation
  -- Formal verification of structural persistence in stochastic systems

require "mathlib" from git "https://github.com/leanprover-community/mathlib4" @ "v4.25.2"

@[default_target]
lean_lib «UPAT» where
  srcDir := "src"
  -- Root: src/UPAT.lean

-- ═══════════════════════════════════════════════════════════════════════════
-- LEGACY: FHDT (Functorial Heat Dominance Theory)
-- ═══════════════════════════════════════════════════════════════════════════
-- This was the original name before the theory expanded into UPAT.
-- Kept for backwards compatibility with early citations and tests.
-- Users should import UPAT, not FHDT.
-- ═══════════════════════════════════════════════════════════════════════════
lean_lib «FHDT» where
  srcDir := "src"

lean_exe «test» where
  root := `test.Main

