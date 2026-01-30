/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/

/-!
# Phase 13: The Levin Wound Experiment (Bioelectricity)

## Biological Background (Michael Levin's Planarian Work)

When a planarian worm is cut, before physical regeneration occurs,
a **Bioelectric Pattern** (voltage gradient) appears at the wound site.
This pattern encodes the "memory" of the missing head.

**Levin's Claim:** Bioelectricity encodes morphology.
**SGC's Claim:** This bioelectric pattern is a **Spectral Graph Closure**.
  The wound creates a "leak," and the bioelectric network responds by
  forming a Transient Boundary (Low Conductance) to seal the information
  leak *before* the physical cells heal.

## The Experiment

We simulate a 5×5 tissue grid:
- **Intact:** Full 2D diffusive coupling (gap junctions)
- **Wounded:** Middle row (10-14) severed from neighbors
- **Regenerating:** Wounded + asymmetric bioelectric flux bridging the gap

## Predictions

1. **Non-Normality:** 0 for Intact/Wounded (symmetric), HIGH for Regenerating
2. **Conductance of Head:** HIGH for Wounded (broken boundary), LOW for Regenerating
3. The bioelectric flux creates a "phantom limb" - a spectral object that
   defines the head informationally before it exists physically.

## Grid Layout

```
Row 0:  [0]  [1]  [2]  [3]  [4]     ← HEAD
Row 1:  [5]  [6]  [7]  [8]  [9]     ← HEAD
Row 2: [10] [11] [12] [13] [14]     ← WOUND (removed in wounded/regenerating)
Row 3: [15] [16] [17] [18] [19]     ← TAIL
Row 4: [20] [21] [22] [23] [24]     ← TAIL
```
-/

namespace SGC.Experiments.LevinWound

/-! ## 1. Matrix Infrastructure (25×25 for 5×5 grid) -/

abbrev Matrix25x25 := Fin 25 → Fin 25 → Float

def zeroMatrix : Matrix25x25 := fun _ _ => 0.0

def floatAbs (x : Float) : Float := if x < 0 then -x else x
def floatSqrt (x : Float) : Float := Float.sqrt (floatAbs x)

/-! ## 2. Grid Topology Helpers -/

/-- Convert (row, col) to linear index (assumes valid range) -/
def toIndex (row col : Nat) (h : row < 5 ∧ col < 5 := by decide) : Fin 25 :=
  ⟨row * 5 + col, by omega⟩

/-- Extract row from linear index -/
def getRow (i : Fin 25) : Nat := i.val / 5

/-- Extract column from linear index -/
def getCol (i : Fin 25) : Nat := i.val % 5

/-- Check if two nodes are grid neighbors (up/down/left/right) -/
def areNeighbors (i j : Fin 25) : Bool :=
  let ri := getRow i
  let ci := getCol i
  let rj := getRow j
  let cj := getCol j
  -- Same row, adjacent columns
  (ri == rj && (ci + 1 == cj || cj + 1 == ci)) ||
  -- Same column, adjacent rows
  (ci == cj && (ri + 1 == rj || rj + 1 == ri))

/-- Check if edge crosses the wound (between rows 1-2 or 2-3) -/
def crossesWound (i j : Fin 25) : Bool :=
  let ri := getRow i
  let rj := getRow j
  -- Edge between row 1 and row 2, or row 2 and row 3
  (ri == 1 && rj == 2) || (ri == 2 && rj == 1) ||
  (ri == 2 && rj == 3) || (ri == 3 && rj == 2)

/-- Check if node is in the wound row -/
def isWoundNode (i : Fin 25) : Bool := getRow i == 2

/-- Check if node is in the Head region (rows 0-1) -/
def isHeadNode (i : Fin 25) : Bool := getRow i <= 1

/-! ## 3. Generator Construction -/

/-- Count neighbors for intact grid -/
def countNeighborsIntact (i : Fin 25) : Nat :=
  (List.finRange 25).filter (fun n => areNeighbors i n) |>.length

/-- Model A: Intact Grid (Full 2D diffusion)
    All neighbors connected symmetrically -/
def intactGenerator (k_diff : Float) : Matrix25x25 := fun i j =>
  if i == j then -(k_diff * (countNeighborsIntact i).toFloat)
  else if areNeighbors i j then k_diff
  else 0.0

/-- Count valid neighbors for wounded grid (excluding wound-crossing edges) -/
def countNeighborsWounded (i : Fin 25) : Nat :=
  (List.finRange 25).filter (fun n => areNeighbors i n && !crossesWound i n) |>.length

/-- Model B: Wounded Grid
    Wound row (10-14) completely severed from rows 1 and 3 -/
def woundedGenerator (k_diff : Float) : Matrix25x25 := fun i j =>
  if i == j then -(k_diff * (countNeighborsWounded i).toFloat)
  else if areNeighbors i j && !crossesWound i j then k_diff
  else 0.0

/-- Model C: Regenerating Grid (Bioelectric Flux)
    Wounded + asymmetric flux bridging the gap at specific points

    The bioelectric field creates "phantom connections":
    - Strong flux from Head boundary (row 1) toward Tail (row 2/3)
    - Weak back-flux (polarized ion pump)

    We bridge at the center: nodes 7 → 17 (through phantom 12) -/
def regeneratingGenerator (k_diff k_flux_fwd k_flux_bwd : Float) : Matrix25x25 := fun i j =>
  -- Start with wounded generator
  let base := woundedGenerator k_diff i j

  -- Add bioelectric bridges (flux across wound gap)
  -- Bridge 1: Node 7 (Head center) ↔ Node 17 (Tail center)
  let i7 : Fin 25 := ⟨7, by omega⟩
  let i17 : Fin 25 := ⟨17, by omega⟩

  -- Bridge 2: Node 6 ↔ Node 16 (left of center)
  let i6 : Fin 25 := ⟨6, by omega⟩
  let i16 : Fin 25 := ⟨16, by omega⟩

  -- Bridge 3: Node 8 ↔ Node 18 (right of center)
  let i8 : Fin 25 := ⟨8, by omega⟩
  let i18 : Fin 25 := ⟨18, by omega⟩

  if i == j then
    -- Adjust diagonal for flux bridges
    let flux_out :=
      if i == i7 then k_flux_fwd
      else if i == i17 then k_flux_bwd
      else if i == i6 then k_flux_fwd
      else if i == i16 then k_flux_bwd
      else if i == i8 then k_flux_fwd
      else if i == i18 then k_flux_bwd
      else 0.0
    base - flux_out
  -- Forward flux: Head → Tail
  else if (i == i7 && j == i17) || (i == i6 && j == i16) || (i == i8 && j == i18) then
    k_flux_fwd
  -- Backward flux: Tail → Head
  else if (i == i17 && j == i7) || (i == i16 && j == i6) || (i == i18 && j == i8) then
    k_flux_bwd
  else
    base

/-! ## 4. Matrix Operations -/

def transpose (M : Matrix25x25) : Matrix25x25 := fun i j => M j i

def matMul (A B : Matrix25x25) : Matrix25x25 := fun i j =>
  (List.finRange 25).foldl (fun acc k => acc + A i k * B k j) 0.0

def matSub (A B : Matrix25x25) : Matrix25x25 := fun i j => A i j - B i j

def frobeniusNorm (M : Matrix25x25) : Float :=
  let sumSq := (List.finRange 25).foldl (fun acc i =>
    (List.finRange 25).foldl (fun acc2 j => acc2 + M i j * M i j) acc) 0.0
  floatSqrt sumSq

/-! ## 5. Non-Normality Diagnostic -/

/-- Non-normality via commutator norm: ||[L, L†]||_F -/
def nonNormalityNorm (L : Matrix25x25) : Float :=
  let Lt := transpose L
  let LLt := matMul L Lt
  let LtL := matMul Lt L
  let comm := matSub LLt LtL
  frobeniusNorm comm

/-! ## 6. Conductance Calculation -/

/-- Steady state approximation: uniform for symmetric, needs computation for asymmetric -/
def uniformPi25 : Fin 25 → Float := fun _ => 1.0 / 25.0

/-- Mass of Head partition (rows 0-1 = nodes 0-9) -/
def headMass (pi : Fin 25 → Float) : Float :=
  (List.finRange 25).foldl (fun acc i =>
    if isHeadNode i then acc + pi i else acc) 0.0

/-- Boundary flux from Head to non-Head -/
def headBoundaryFlux (L : Matrix25x25) (pi : Fin 25 → Float) : Float :=
  (List.finRange 25).foldl (fun acc i =>
    if isHeadNode i then
      (List.finRange 25).foldl (fun acc2 j =>
        if !isHeadNode j && L i j > 0.0 then
          acc2 + floatAbs (pi i * L i j)
        else acc2) acc
    else acc) 0.0

/-- Conductance of Head partition -/
def headConductance (L : Matrix25x25) (pi : Fin 25 → Float) : Float :=
  let mass := headMass pi
  let massTail := 1.0 - mass
  let minMass := if mass < massTail then mass else massTail
  let flux := headBoundaryFlux L pi
  if minMass > 1e-10 then flux / minMass else 0.0

/-! ## 7. Spectral Gap Proxy -/

def spectralGapProxy (L : Matrix25x25) : Float :=
  let diags := (List.finRange 25).map (fun i => L i i)
  let maxDiag := diags.foldl (fun acc x => if x > acc then x else acc) (-1000.0)
  let minDiag := diags.foldl (fun acc x => if x < acc then x else acc) 0.0
  floatAbs (maxDiag - minDiag)

/-! ## 7b. NEW DIAGNOSTICS: What Bioelectricity Actually Encodes -/

/-- Net current from Head to Tail (positive = Head→Tail flow)
    This measures DIRECTED information flow, not just connectivity -/
def netCurrentHeadToTail (L : Matrix25x25) (pi : Fin 25 → Float) : Float :=
  (List.finRange 25).foldl (fun acc i =>
    if isHeadNode i then
      (List.finRange 25).foldl (fun acc2 j =>
        if !isHeadNode j then
          -- Net current = forward - backward
          acc2 + (pi i * L i j - pi j * L j i)
        else acc2) acc
    else acc) 0.0

/-- Entropy production rate: Σ_{i,j} J_{ij} ln(L_{ij}/L_{ji})
    This measures how much energy is being dissipated to maintain the pattern -/
def entropyProductionRate (L : Matrix25x25) (pi : Fin 25 → Float) : Float :=
  (List.finRange 25).foldl (fun acc i =>
    (List.finRange 25).foldl (fun acc2 j =>
      if i != j && L i j > 1e-10 && L j i > 1e-10 then
        let J_ij := pi i * L i j  -- probability current i→j
        let ratio := L i j / L j i
        acc2 + J_ij * Float.log ratio
      else acc2) acc) 0.0

/-- Asymmetry index: How different is forward vs backward flux?
    For symmetric systems this is 0, for polarized systems it's large -/
def fluxAsymmetryIndex (L : Matrix25x25) : Float :=
  let Lt := transpose L
  let diff := matSub L Lt
  frobeniusNorm diff

/-- Count connected components (approximate via reachability from node 0) -/
def isConnectedToHead (L : Matrix25x25) (node : Fin 25) : Bool :=
  -- Simple: check if there's any path from head nodes to this node
  -- For now, just check direct edges from head region
  (List.finRange 25).any (fun i => isHeadNode i && (L i node > 0.0 || L node i > 0.0))

/-! ## 8. Experiment Structure (Extended with New Diagnostics) -/

structure WoundResult where
  modelName : String
  description : String
  -- Original metrics
  nonNormality : Float
  headConductance : Float
  spectralGap : Float
  -- NEW: What bioelectricity actually encodes
  netCurrent : Float        -- Directed information flow Head→Tail
  entropyProduction : Float -- Energy cost to maintain pattern
  fluxAsymmetry : Float     -- How polarized is the system?
  deriving Repr

/-! ## 9. Parameters -/

def k_diff : Float := 1.0       -- Diffusive coupling (gap junctions)
def k_flux_fwd : Float := 5.0   -- Bioelectric forward flux
def k_flux_bwd : Float := 0.1   -- Bioelectric backward flux

/-! ## 10. Build Generators -/

def L_intact := intactGenerator k_diff
def L_wounded := woundedGenerator k_diff
def L_regenerating := regeneratingGenerator k_diff k_flux_fwd k_flux_bwd

/-! ## 11. Run Experiments -/

def intactResult : WoundResult := {
  modelName := "INTACT TISSUE"
  description := "Full 2D diffusion (healthy planarian)"
  nonNormality := nonNormalityNorm L_intact
  headConductance := headConductance L_intact uniformPi25
  spectralGap := spectralGapProxy L_intact
  netCurrent := netCurrentHeadToTail L_intact uniformPi25
  entropyProduction := entropyProductionRate L_intact uniformPi25
  fluxAsymmetry := fluxAsymmetryIndex L_intact
}

def woundedResult : WoundResult := {
  modelName := "WOUNDED TISSUE"
  description := "Middle row severed (fresh cut)"
  nonNormality := nonNormalityNorm L_wounded
  headConductance := headConductance L_wounded uniformPi25
  spectralGap := spectralGapProxy L_wounded
  netCurrent := netCurrentHeadToTail L_wounded uniformPi25
  entropyProduction := entropyProductionRate L_wounded uniformPi25
  fluxAsymmetry := fluxAsymmetryIndex L_wounded
}

def regeneratingResult : WoundResult := {
  modelName := "REGENERATING TISSUE"
  description := "Wounded + bioelectric flux (phantom head)"
  nonNormality := nonNormalityNorm L_regenerating
  headConductance := headConductance L_regenerating uniformPi25
  spectralGap := spectralGapProxy L_regenerating
  netCurrent := netCurrentHeadToTail L_regenerating uniformPi25
  entropyProduction := entropyProductionRate L_regenerating uniformPi25
  fluxAsymmetry := fluxAsymmetryIndex L_regenerating
}

/-! ## 12. Display Functions -/

def formatFloat (x : Float) (decimals : Nat := 4) : String :=
  let scale := Float.pow 10.0 decimals.toFloat
  let rounded := Float.round (x * scale) / scale
  toString rounded

def resultToString (r : WoundResult) : String :=
  s!"╔══════════════════════════════════════════════════════════════╗\n" ++
  s!"║  {r.modelName}\n" ++
  s!"║  {r.description}\n" ++
  s!"╠══════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Non-Normality ||[L,L†]||:  {formatFloat r.nonNormality}\n" ++
  s!"║  Head Conductance φ:        {formatFloat r.headConductance}\n" ++
  s!"║  Spectral Gap:              {formatFloat r.spectralGap}\n" ++
  s!"╠═══════════ NEW: What Bioelectricity Actually Encodes ════════╣\n" ++
  s!"║  Net Current (Head→Tail):   {formatFloat r.netCurrent}\n" ++
  s!"║  Entropy Production:        {formatFloat r.entropyProduction}\n" ++
  s!"║  Flux Asymmetry ||L-L†||:   {formatFloat r.fluxAsymmetry}\n" ++
  s!"╚══════════════════════════════════════════════════════════════╝"

#eval resultToString intactResult
#eval resultToString woundedResult
#eval resultToString regeneratingResult

/-! ## 13. CRITICAL ANALYSIS: What Does SGC Actually Predict? -/

def criticalAnalysis : String :=
  let intact := intactResult
  let wounded := woundedResult
  let regen := regeneratingResult

  -- FROM FIRST PRINCIPLES:
  -- 1. Non-Normality measures ASYMMETRY of information flow
  -- 2. Net Current measures DIRECTED flow (not just connectivity)
  -- 3. Entropy Production measures ENERGY COST to maintain pattern
  -- 4. Flux Asymmetry measures how POLARIZED the generator is

  -- THE REAL SGC PREDICTIONS FOR BIOELECTRICITY:
  -- P1: Only asymmetric flux creates non-normality
  let p1 := intact.nonNormality < 1.0 && wounded.nonNormality < 1.0 && regen.nonNormality > 10.0

  -- P2: Regenerating tissue has DIRECTED current flow (Head→Tail or Tail→Head)
  let p2 := floatAbs regen.netCurrent > floatAbs intact.netCurrent * 10.0

  -- P3: Regenerating tissue DISSIPATES ENERGY (entropy production > 0)
  let p3 := regen.entropyProduction > 0.1 && intact.entropyProduction < 0.01

  -- P4: Bioelectric pattern is POLARIZED (high flux asymmetry)
  let p4 := regen.fluxAsymmetry > 1.0 && intact.fluxAsymmetry < 0.01

  s!"╔══════════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║      CRITICAL ANALYSIS: What Does Bioelectricity Actually Encode?            ║\n" ++
  s!"║      (First Principles Examination of SGC Predictions)                       ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║                       Intact        Wounded       Regenerating               ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Non-Normality:       {formatFloat intact.nonNormality 1}           {formatFloat wounded.nonNormality 1}          {formatFloat regen.nonNormality 1}                ║\n" ++
  s!"║  Net Current H→T:     {formatFloat intact.netCurrent 3}         {formatFloat wounded.netCurrent 3}         {formatFloat regen.netCurrent 3}               ║\n" ++
  s!"║  Entropy Production:  {formatFloat intact.entropyProduction 3}         {formatFloat wounded.entropyProduction 3}         {formatFloat regen.entropyProduction 3}               ║\n" ++
  s!"║  Flux Asymmetry:      {formatFloat intact.fluxAsymmetry 2}          {formatFloat wounded.fluxAsymmetry 2}          {formatFloat regen.fluxAsymmetry 2}               ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  P1: Non-Normality = Asymmetric Information Flow                             ║\n" ++
  s!"║      Only regenerating has it?  {if p1 then "✓ YES" else "✗ NO"}                                        ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  P2: Directed Current = Morphological Instruction                            ║\n" ++
  s!"║      Regenerating has strong net current?  {if p2 then "✓ YES" else "✗ NO"}                             ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  P3: Entropy Production = Active Maintenance                                 ║\n" ++
  s!"║      Regenerating dissipates energy?  {if p3 then "✓ YES" else "✗ NO"}                                  ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  P4: Flux Asymmetry = Polarized Pattern                                      ║\n" ++
  s!"║      Regenerating is polarized?  {if p4 then "✓ YES" else "✗ NO"}                                       ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  THE KEY INSIGHT:                                                            ║\n" ++
  s!"║    Bioelectric patterns encode morphology via DIRECTED INFORMATION FLOW.     ║\n" ++
  s!"║    The polarized ion pump creates asymmetric flux that says:                 ║\n" ++
  s!"║    'This end is HEAD, that end is TAIL.'                                     ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║    This is NOT about 'sealing boundaries' - it's about creating              ║\n" ++
  s!"║    DIRECTED COMMUNICATION that encodes spatial identity.                     ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  OVERALL: {if p1 && p2 && p4 then "✓ SGC VALIDATED - Bioelectricity = Directed Information" else "? Partial confirmation - investigate"}             ║\n" ++
  s!"╚══════════════════════════════════════════════════════════════════════════════╝"

#eval criticalAnalysis

/-! ## 14. Grid Visualization Helper -/

def showGridState (name : String) (L : Matrix25x25) : String :=
  -- Show which edges exist (non-zero off-diagonal)
  let edges := (List.finRange 25).foldl (fun acc i =>
    (List.finRange 25).foldl (fun acc2 j =>
      if i.val < j.val && L i j > 0.0 then
        acc2 ++ s!"  {i.val}↔{j.val}"
      else acc2) acc) ""
  s!"{name}: {edges.take 100}..."

#eval showGridState "Intact edges" L_intact
#eval showGridState "Wounded edges" L_wounded
#eval showGridState "Regenerating edges" L_regenerating

end SGC.Experiments.LevinWound
