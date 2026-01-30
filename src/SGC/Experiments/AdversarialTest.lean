/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/

/-!
# Mathematical Demonstration: Linear Chain vs Closed Cycle

This module compares SGC metrics on two **synthetic topologies**.

## Purpose

Demonstrate that conductance distinguishes:
- **Open chain**: Probability flows through and exits
- **Closed cycle**: Probability recirculates

## Models (Synthetic)

**Model A - Linear Chain:** 0 → 1 → 2 → 3 → 4 → 5 (open ends)
**Model B - Closed Cycle:** 0 → 1 → 2 → 3 → 4 → 5 → 0 (periodic)

Both use identical rate parameters.

## Mathematical Predictions

For partition {0,1,2} vs {3,4,5}:
- **Chain**: Higher conductance (boundary is permeable)
- **Cycle**: Lower conductance (information recirculates)

## Limitations

This is a mathematical demonstration of topological effects on conductance.
It does NOT validate claims about biological systems.
-/

namespace SGC.Experiments.AdversarialTest

/-! ## 1. Matrix Infrastructure (reused from MetabolicCore) -/

def Matrix6x6 := Fin 6 → Fin 6 → Float

instance : Inhabited Matrix6x6 := ⟨fun _ _ => 0.0⟩

def Matrix6x6.zero : Matrix6x6 := fun _ _ => 0.0

def Matrix6x6.add (A B : Matrix6x6) : Matrix6x6 := fun i j => A i j + B i j

def Matrix6x6.sub (A B : Matrix6x6) : Matrix6x6 := fun i j => A i j - B i j

def Matrix6x6.mul (A B : Matrix6x6) : Matrix6x6 := fun i j =>
  (List.finRange 6).foldl (fun acc k => acc + A i k * B k j) 0.0

def Matrix6x6.transpose (A : Matrix6x6) : Matrix6x6 := fun i j => A j i

def floatAbs (x : Float) : Float := if x < 0.0 then -x else x

def floatMax (a b : Float) : Float := if a > b then a else b

def floatMin (a b : Float) : Float := if a < b then a else b

/-! ## 2. Generator Definitions -/

/-- Model A: Linear Chain (The "Drain")
    0 → 1 → 2 → 3 → 4 → 5 with open boundaries
    State 0 is source-like, State 5 is sink-like -/
def linearChainGenerator (k_fwd k_bwd : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  -- Forward: i → i+1 (for i < 5)
  if i_val < 5 && j_val == i_val + 1 then k_fwd
  -- Backward: i → i-1 (for i > 0)
  else if i_val > 0 && j_val == i_val - 1 then k_bwd
  -- Diagonal: negative sum of outgoing rates
  else if i_val == j_val then
    if i_val == 0 then -k_fwd           -- Node 0: only outgoing to 1
    else if i_val == 5 then -k_bwd      -- Node 5: only outgoing to 4
    else -(k_fwd + k_bwd)               -- Interior nodes: both directions
  else 0.0

/-- Model B: Cycle (The "Cell")
    0 → 1 → 2 → 3 → 4 → 5 → 0 with periodic boundaries -/
def cycleGenerator (k_fwd k_bwd : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  let next := (i_val + 1) % 6
  let prev := (i_val + 5) % 6
  if j_val == next then k_fwd
  else if j_val == prev then k_bwd
  else if i_val == j_val then -(k_fwd + k_bwd)
  else 0.0

/-! ## 3. Steady-State Distribution -/

/-- For the cycle with uniform initial, steady state is uniform -/
def uniformPi : Fin 6 → Float := fun _ => 1.0 / 6.0

/-- For linear chain with absorbing boundaries, steady state concentrates at sink.
    Approximate with a gradient distribution. -/
def gradientPi (k_fwd k_bwd : Float) : Fin 6 → Float := fun i =>
  -- Ratio r = k_fwd/k_bwd determines gradient steepness
  let r := k_fwd / k_bwd
  -- Unnormalized: π_i ∝ (k_bwd/k_fwd)^i = r^(-i)
  let unnorm := Float.pow (1.0 / r) i.val.toFloat
  -- Normalize (geometric series sum)
  let total := (List.finRange 6).foldl (fun acc j =>
    acc + Float.pow (1.0 / r) j.val.toFloat) 0.0
  unnorm / total

/-! ## 4. Entropy Production Rate -/

/-- Probability current J_{ij} = π_i * L_{ij} - π_j * L_{ji} -/
def probabilityCurrent (L : Matrix6x6) (pi_dist : Fin 6 → Float) (i j : Fin 6) : Float :=
  pi_dist i * L i j - pi_dist j * L j i

/-- Total entropy production rate: σ = Σ_{i<j} J_{ij} * ln(π_i L_{ij} / π_j L_{ji}) -/
def entropyProductionRate (L : Matrix6x6) (pi_dist : Fin 6 → Float) : Float :=
  (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j =>
      if i.val < j.val then
        let J_ij := probabilityCurrent L pi_dist i j
        let num := pi_dist i * L i j
        let den := pi_dist j * L j i
        if num > 1e-10 && den > 1e-10 then
          acc2 + J_ij * Float.log (num / den)
        else acc2
      else acc2) acc) 0.0

/-- Total probability current magnitude -/
def totalCurrentMagnitude (L : Matrix6x6) (pi_dist : Fin 6 → Float) : Float :=
  (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j =>
      if i.val < j.val then
        acc2 + floatAbs (probabilityCurrent L pi_dist i j)
      else acc2) acc) 0.0

/-! ## 5. q-Escort Conductance -/

/-- Escort distribution for q=1 (standard case): ψ^(q)_i = π_i^q / Σ π_j^q -/
def escortDistribution (pi_dist : Fin 6 → Float) (q : Float) : Fin 6 → Float := fun i =>
  let pi_q_i := Float.pow (pi_dist i) q
  let Z := (List.finRange 6).foldl (fun acc j => acc + Float.pow (pi_dist j) q) 0.0
  if Z > 1e-10 then pi_q_i / Z else 1.0 / 6.0

/-- Boundary measure for partition S = {0,1,2} vs S^c = {3,4,5}
    ∂S = {edges crossing between S and S^c} -/
def boundaryFlux (L : Matrix6x6) (pi_dist : Fin 6 → Float) : Float :=
  -- Edges crossing: (2,3) and (3,2) for linear chain
  -- For cycle also: (5,0) and (0,5)
  let flux_2_3 := floatAbs (pi_dist ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi_dist ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  flux_2_3 + flux_3_2

/-- Boundary flux including cycle wrap-around (5↔0) -/
def boundaryFluxCycle (L : Matrix6x6) (pi_dist : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi_dist ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi_dist ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  let flux_5_0 := floatAbs (pi_dist ⟨5, by omega⟩ * L ⟨5, by omega⟩ ⟨0, by omega⟩)
  let flux_0_5 := floatAbs (pi_dist ⟨0, by omega⟩ * L ⟨0, by omega⟩ ⟨5, by omega⟩)
  flux_2_3 + flux_3_2 + flux_5_0 + flux_0_5

/-- Escort mass of subset S = {0,1,2} -/
def escortMassS (psi : Fin 6 → Float) : Float :=
  psi ⟨0, by omega⟩ + psi ⟨1, by omega⟩ + psi ⟨2, by omega⟩

/-- q-Escort Conductance: φ_q(S) = boundary_flux / min(ψ(S), ψ(S^c)) -/
def escortConductance (L : Matrix6x6) (pi_dist : Fin 6 → Float) (q : Float) (isCycle : Bool) : Float :=
  let psi := escortDistribution pi_dist q
  let mass_S := escortMassS psi
  let mass_Sc := 1.0 - mass_S
  let minMass := floatMin mass_S mass_Sc
  let flux := if isCycle then boundaryFluxCycle L pi_dist else boundaryFlux L pi_dist
  if minMass > 1e-10 then flux / minMass else 0.0

/-! ## 6. Non-Normality (Commutator Norm) -/

/-- Commutator [L, L†] = L·L† - L†·L -/
def commutator (L : Matrix6x6) : Matrix6x6 :=
  let Lt := Matrix6x6.transpose L
  Matrix6x6.sub (Matrix6x6.mul L Lt) (Matrix6x6.mul Lt L)

/-- Frobenius norm of commutator -/
def commutatorNorm (L : Matrix6x6) : Float :=
  let C := commutator L
  let sumSq := (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j => acc2 + C i j * C i j) acc) 0.0
  Float.sqrt sumSq

/-! ## 7. Experiment Structure -/

structure AdversarialResult where
  modelName : String
  topology : String
  k_fwd : Float
  k_bwd : Float
  entropyProduction : Float
  totalCurrent : Float
  conductance_q1 : Float
  commutatorNorm : Float
  deriving Repr

def runDrainExperiment (k_fwd k_bwd : Float) : AdversarialResult :=
  let L := linearChainGenerator k_fwd k_bwd
  let pi := gradientPi k_fwd k_bwd
  {
    modelName := "THE DRAIN"
    topology := "Linear Chain (Open)"
    k_fwd := k_fwd
    k_bwd := k_bwd
    entropyProduction := entropyProductionRate L pi
    totalCurrent := totalCurrentMagnitude L pi
    conductance_q1 := escortConductance L pi 1.0 false
    commutatorNorm := commutatorNorm L
  }

def runCellExperiment (k_fwd k_bwd : Float) : AdversarialResult :=
  let L := cycleGenerator k_fwd k_bwd
  let pi := uniformPi
  {
    modelName := "THE CELL"
    topology := "Cycle (Periodic)"
    k_fwd := k_fwd
    k_bwd := k_bwd
    entropyProduction := entropyProductionRate L pi
    totalCurrent := totalCurrentMagnitude L pi
    conductance_q1 := escortConductance L pi 1.0 true
    commutatorNorm := commutatorNorm L
  }

/-! ## 8. Display Functions -/

def formatFloat (x : Float) (decimals : Nat := 4) : String :=
  let scale := Float.pow 10.0 decimals.toFloat
  let rounded := Float.round (x * scale) / scale
  toString rounded

def resultToString (r : AdversarialResult) : String :=
  s!"╔══════════════════════════════════════════════════════════════╗\n" ++
  s!"║  {r.modelName}\n" ++
  s!"║  Topology: {r.topology}\n" ++
  s!"╠══════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Flux: k_fwd = {formatFloat r.k_fwd 1}, k_bwd = {formatFloat r.k_bwd 1}\n" ++
  s!"║\n" ++
  s!"║  THERMODYNAMICS:\n" ++
  s!"║    Entropy Production σ:  {formatFloat r.entropyProduction}\n" ++
  s!"║    Total Current |J|:     {formatFloat r.totalCurrent}\n" ++
  s!"║\n" ++
  s!"║  SGC DIAGNOSTICS:\n" ++
  s!"║    Commutator ||[L,L†]||: {formatFloat r.commutatorNorm}\n" ++
  s!"║    q-Conductance (q=1):   {formatFloat r.conductance_q1}\n" ++
  s!"╚══════════════════════════════════════════════════════════════╝"

/-! ## 9. Run the Adversarial Test -/

def k_fwd_test : Float := 10.0
def k_bwd_test : Float := 0.1

def drainResult := runDrainExperiment k_fwd_test k_bwd_test
def cellResult := runCellExperiment k_fwd_test k_bwd_test

#eval resultToString drainResult
#eval resultToString cellResult

/-! ## 10. Comparison Summary -/

def comparisonSummary : String :=
  let drain := drainResult
  let cell := cellResult
  let conductanceRatio := if cell.conductance_q1 > 1e-10
    then drain.conductance_q1 / cell.conductance_q1
    else 0.0
  let verdict := if drain.conductance_q1 > cell.conductance_q1 * 1.5 then
    "✓ SGC VALIDATED: Drain has HIGHER conductance than Cell"
  else if drain.conductance_q1 < cell.conductance_q1 * 0.67 then
    "✗ SGC FALSIFIED: Drain has LOWER conductance than Cell"
  else
    "? INCONCLUSIVE: Conductances are similar"

  s!"╔══════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║                    ADVERSARIAL TEST: GRADIENT vs CYCLE                   ║\n" ++
  s!"║                    Phase 10: Falsifiability Experiment                   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║                          DRAIN (Linear)    CELL (Cycle)                  ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Entropy σ:              {formatFloat drain.entropyProduction 2}              {formatFloat cell.entropyProduction 2}                   ║\n" ++
  s!"║  Current |J|:            {formatFloat drain.totalCurrent 2}              {formatFloat cell.totalCurrent 2}                    ║\n" ++
  s!"║  ||[L,L†]||:             {formatFloat drain.commutatorNorm 2}               {formatFloat cell.commutatorNorm 2}                     ║\n" ++
  s!"║  Conductance φ:          {formatFloat drain.conductance_q1 2}              {formatFloat cell.conductance_q1 2}                   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Conductance Ratio (Drain/Cell): {formatFloat conductanceRatio 2}x                              ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  VERDICT: {verdict}  ║\n" ++
  s!"╚══════════════════════════════════════════════════════════════════════════╝"

#eval comparisonSummary

/-! ## 11. Matrix Inspection -/

def showMatrix (name : String) (M : Matrix6x6) : String :=
  let rows := (List.finRange 6).map fun i =>
    let cols := (List.finRange 6).map fun j => formatFloat (M i j) 2
    String.intercalate "  " cols
  s!"{name}:\n" ++ String.intercalate "\n" rows

def L_drain := linearChainGenerator k_fwd_test k_bwd_test
def L_cell := cycleGenerator k_fwd_test k_bwd_test

#eval showMatrix "L_drain (Linear Chain)" L_drain
#eval showMatrix "L_cell (Cycle)" L_cell

#eval s!"Gradient π (Drain): {(List.finRange 6).map (fun i => formatFloat (gradientPi k_fwd_test k_bwd_test i) 4)}"
#eval s!"Uniform π (Cell): {(List.finRange 6).map (fun i => formatFloat (uniformPi i) 4)}"

end SGC.Experiments.AdversarialTest
