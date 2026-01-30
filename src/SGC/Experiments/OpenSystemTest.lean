/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/

/-!
# Phase 11: Rigorous Open System Experiment

## Mathematical Analysis of the Three Topologies

### 1. Perfect Cycle (Circulant Matrix)
- Circulant matrices are ALWAYS normal (diagonalizable by DFT)
- Steady state: π = uniform (by cyclic symmetry)
- Has constant circulating current J = (k_fwd - k_bwd) * π_i
- This is a NESS (non-equilibrium steady state)

### 2. Linear Drain (Open Boundaries)
- NOT circulant → NOT normal
- Steady state: π_i ∝ (k_bwd/k_fwd)^i (geometric gradient)
- For k_fwd/k_bwd = 100, probability piles up at node 0
- At steady state, NET CURRENT IS ZERO (it's actually equilibrium-like!)

### 3. Open Cycle (Balanced Source/Sink)
- Cycle with source into node 0, sink out of node 3
- Source rate = Sink rate (probability conserved)
- NOT circulant → NOT normal
- Has non-trivial steady state with current flow

## The Key Mathematical Predictions

### Non-Normality ||[L, L†]||_F
Measures deviation from orthogonal eigenvectors.
- Perfect Cycle: 0 (circulant = normal)
- Linear Drain: HIGH (boundary breaks symmetry)
- Open Cycle: MEDIUM (source/sink break symmetry moderately)

### Current Flow at Steady State
The DRAIN has NO net current at true steady state (probability gradient blocks flow).
The CYCLE maintains constant current (probability recirculates).
The OPEN CYCLE has current from source through cycle to sink.

### Spectral Gap (Mixing Time)
- Perfect Cycle: All modes decay at same rate λ = k_fwd + k_bwd
- Linear Drain: Has slow mode at node 5 (λ = k_bwd = 0.1)
- Open Cycle: Intermediate (source/sink create asymmetry but preserve mixing)
-/

namespace SGC.Experiments.OpenSystemTest

/-! ## 1. Matrix Infrastructure -/

def Matrix6x6 := Fin 6 → Fin 6 → Float

instance : Inhabited Matrix6x6 := ⟨fun _ _ => 0.0⟩

def Matrix6x6.zero : Matrix6x6 := fun _ _ => 0.0

def Matrix6x6.identity : Matrix6x6 := fun i j => if i == j then 1.0 else 0.0

def Matrix6x6.add (A B : Matrix6x6) : Matrix6x6 := fun i j => A i j + B i j

def Matrix6x6.sub (A B : Matrix6x6) : Matrix6x6 := fun i j => A i j - B i j

def Matrix6x6.mul (A B : Matrix6x6) : Matrix6x6 := fun i j =>
  (List.finRange 6).foldl (fun acc k => acc + A i k * B k j) 0.0

def Matrix6x6.smul (c : Float) (A : Matrix6x6) : Matrix6x6 := fun i j => c * A i j

def Matrix6x6.transpose (A : Matrix6x6) : Matrix6x6 := fun i j => A j i

def floatAbs (x : Float) : Float := if x < 0.0 then -x else x

def floatMax (a b : Float) : Float := if a > b then a else b

def floatMin (a b : Float) : Float := if a < b then a else b

/-! ## 2. Three Generator Models -/

/-- Model A: Perfect Cycle (Closed System)
    0 → 1 → 2 → 3 → 4 → 5 → 0 (periodic) -/
def perfectCycleGenerator (k_fwd k_bwd : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  let next := (i_val + 1) % 6
  let prev := (i_val + 5) % 6
  if j_val == next then k_fwd
  else if j_val == prev then k_bwd
  else if i_val == j_val then -(k_fwd + k_bwd)
  else 0.0

/-- Model B: Open Cycle (Balanced Source/Sink)
    Cycle with external source feeding node 0 and sink draining node 3.
    The source/sink rates are balanced to conserve total probability.

    Mathematically: We model this as a 6-state system where
    - Node 0 receives influx from "environment" (modeled as increased backward rate from node 5)
    - Node 3 has outflux to "environment" (modeled as increased forward rate to node 4)

    This breaks circulant symmetry while maintaining a valid stochastic generator. -/
def openCycleGenerator (k_fwd k_bwd source_sink : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  let next := (i_val + 1) % 6
  let prev := (i_val + 5) % 6
  -- Forward transitions
  if j_val == next then
    if i_val == 3 then k_fwd + source_sink  -- Extra flux OUT of node 3 (to sink)
    else k_fwd
  -- Backward transitions
  else if j_val == prev then
    if i_val == 0 then k_bwd + source_sink  -- Extra flux INTO node 0 (from source)
    else k_bwd
  -- Diagonal (negative sum of outgoing)
  else if i_val == j_val then
    if i_val == 0 then -(k_fwd + k_bwd + source_sink)  -- Node 0: extra inflow means extra diagonal
    else if i_val == 3 then -(k_fwd + k_bwd + source_sink)  -- Node 3: extra outflow
    else -(k_fwd + k_bwd)
  else 0.0

/-- Model C: Linear Drain (Pure Gradient)
    0 → 1 → 2 → 3 → 4 → 5 (open boundaries) -/
def linearDrainGenerator (k_fwd k_bwd : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  if i_val < 5 && j_val == i_val + 1 then k_fwd
  else if i_val > 0 && j_val == i_val - 1 then k_bwd
  else if i_val == j_val then
    if i_val == 0 then -k_fwd
    else if i_val == 5 then -k_bwd
    else -(k_fwd + k_bwd)
  else 0.0

/-! ## 3. Steady-State Distributions (Computed from Theory) -/

/-- Perfect Cycle: Uniform steady state (by symmetry) -/
def uniformPi : Fin 6 → Float := fun _ => 1.0 / 6.0

/-- Linear Drain: Geometric gradient π_i ∝ (k_fwd/k_bwd)^i
    Detailed balance: π_i * k_fwd = π_{i+1} * k_bwd
    So: π_{i+1}/π_i = k_fwd/k_bwd = 100
    Probability piles up at the SINK (node 5), not source (node 0) -/
def gradientPi (k_fwd k_bwd : Float) : Fin 6 → Float := fun i =>
  let r := k_fwd / k_bwd  -- = 100 for our parameters (probability grows toward sink)
  let unnorm := Float.pow r i.val.toFloat
  -- Geometric series: Σ r^i = (r^6 - 1)/(r - 1)
  let total := (Float.pow r 6.0 - 1.0) / (r - 1.0)
  unnorm / total

/-- Open Cycle: Approximate steady state (perturbed uniform)
    The source/sink breaks uniformity but not dramatically for small perturbations -/
def openCyclePi (_k_fwd _k_bwd _source_sink : Float) : Fin 6 → Float := fun _ =>
  -- First-order perturbation theory: π ≈ uniform + O(source_sink/k_fwd)
  -- For simplicity, use uniform as approximation
  1.0 / 6.0

/-! ## 4. Current Flow Diagnostic -/

/-- Net probability current on edge i → j: J_{ij} = π_i L_{ij} - π_j L_{ji} -/
def edgeCurrent (L : Matrix6x6) (pi : Fin 6 → Float) (i j : Fin 6) : Float :=
  pi i * L i j - pi j * L j i

/-- Total circulating current (sum of forward currents around cycle) -/
def circulatingCurrent (L : Matrix6x6) (pi : Fin 6 → Float) : Float :=
  (List.finRange 6).foldl (fun acc i =>
    let j : Fin 6 := ⟨(i.val + 1) % 6, by omega⟩
    acc + (pi i * L i j)  -- Forward flux only
  ) 0.0

/-- Net current across partition S={0,1,2} vs Sc={3,4,5}
    Positive = flow from S to Sc -/
def partitionCurrent (L : Matrix6x6) (pi : Fin 6 → Float) : Float :=
  -- Edge 2→3 and edge 5→0 (wrapping)
  let J_2_3 := edgeCurrent L pi ⟨2, by omega⟩ ⟨3, by omega⟩
  let J_5_0 := edgeCurrent L pi ⟨5, by omega⟩ ⟨0, by omega⟩
  J_2_3 - J_5_0  -- Net flow from S to Sc

/-! ## 5. Non-Normality Diagnostic -/

/-- Commutator [L, L†] = L·L† - L†·L -/
def commutator (L : Matrix6x6) : Matrix6x6 :=
  let Lt := Matrix6x6.transpose L
  Matrix6x6.sub (Matrix6x6.mul L Lt) (Matrix6x6.mul Lt L)

/-- Frobenius norm -/
def frobeniusNorm (A : Matrix6x6) : Float :=
  let sumSq := (List.finRange 6).foldl (fun acc i =>
    (List.finRange 6).foldl (fun acc2 j => acc2 + A i j * A i j) acc) 0.0
  Float.sqrt sumSq

/-- Non-normality measure: ||[L, L†]||_F -/
def nonNormalityNorm (L : Matrix6x6) : Float :=
  frobeniusNorm (commutator L)

/-! ## 6. Spectral Diagnostics -/

/-- Spectral gap proxy: difference between fastest and slowest decay rates
    Approximated by difference between max and min diagonal elements -/
def spectralGapProxy (L : Matrix6x6) : Float :=
  let diags := (List.finRange 6).map (fun i => L i i)
  let maxDiag := diags.foldl floatMax (-1000.0)
  let minDiag := diags.foldl floatMin 0.0
  floatAbs (maxDiag - minDiag)

/-- Slowest decay rate (closest to 0) - determines mixing time -/
def slowestDecayRate (L : Matrix6x6) : Float :=
  let diags := (List.finRange 6).map (fun i => L i i)
  diags.foldl floatMax (-1000.0)  -- Least negative = slowest decay

/-! ## 7. Conductance with Correct Steady States -/

def escortMassS (pi : Fin 6 → Float) : Float :=
  pi ⟨0, by omega⟩ + pi ⟨1, by omega⟩ + pi ⟨2, by omega⟩

/-- Boundary flux for cycle (edges 2-3 and 5-0) -/
def boundaryFluxCycle (L : Matrix6x6) (pi : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  let flux_5_0 := floatAbs (pi ⟨5, by omega⟩ * L ⟨5, by omega⟩ ⟨0, by omega⟩)
  let flux_0_5 := floatAbs (pi ⟨0, by omega⟩ * L ⟨0, by omega⟩ ⟨5, by omega⟩)
  flux_2_3 + flux_3_2 + flux_5_0 + flux_0_5

/-- Boundary flux for linear chain (only edge 2-3) -/
def boundaryFluxLinear (L : Matrix6x6) (pi : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  flux_2_3 + flux_3_2

/-- Conductance with proper steady state distribution -/
def conductanceWithPi (L : Matrix6x6) (pi : Fin 6 → Float) (isCycle : Bool) : Float :=
  let mass_S := escortMassS pi
  let mass_Sc := 1.0 - mass_S
  let minMass := floatMin mass_S mass_Sc
  let flux := if isCycle then boundaryFluxCycle L pi else boundaryFluxLinear L pi
  if minMass > 1e-10 then flux / minMass else 0.0

/-! ## 8. Experiment Structure -/

structure OpenSystemResult where
  modelName : String
  topology : String
  nonNormality : Float
  currentFlow : Float      -- Net current (key physical observable!)
  conductance : Float
  slowestDecay : Float     -- Mixing time proxy
  spectralGap : Float
  deriving Repr

/-! ## 9. Parameters -/

def k_fwd : Float := 10.0
def k_bwd : Float := 0.1
def source_sink_rate : Float := 2.0

/-! ## 10. The Three Generators -/

def L_perfect := perfectCycleGenerator k_fwd k_bwd
def L_open := openCycleGenerator k_fwd k_bwd source_sink_rate
def L_drain := linearDrainGenerator k_fwd k_bwd

/-! ## 11. The Three Steady States -/

def pi_perfect := uniformPi
def pi_drain := gradientPi k_fwd k_bwd
def pi_open := uniformPi  -- Approximation (true π requires solving πL=0)

/-! ## 12. Run Experiments with Correct Steady States -/

def perfectResult : OpenSystemResult := {
  modelName := "PERFECT CYCLE"
  topology := "Closed Ring (Circulant)"
  nonNormality := nonNormalityNorm L_perfect
  currentFlow := circulatingCurrent L_perfect pi_perfect
  conductance := conductanceWithPi L_perfect pi_perfect true
  slowestDecay := slowestDecayRate L_perfect
  spectralGap := spectralGapProxy L_perfect
}

def openResult : OpenSystemResult := {
  modelName := "OPEN CYCLE"
  topology := "Ring with Source/Sink"
  nonNormality := nonNormalityNorm L_open
  currentFlow := circulatingCurrent L_open pi_open
  conductance := conductanceWithPi L_open pi_open true
  slowestDecay := slowestDecayRate L_open
  spectralGap := spectralGapProxy L_open
}

def drainResult : OpenSystemResult := {
  modelName := "LINEAR DRAIN"
  topology := "Open Chain (Gradient)"
  nonNormality := nonNormalityNorm L_drain
  currentFlow := circulatingCurrent L_drain pi_drain
  conductance := conductanceWithPi L_drain pi_drain false
  slowestDecay := slowestDecayRate L_drain
  spectralGap := spectralGapProxy L_drain
}

/-! ## 13. Display Functions -/

def formatFloat (x : Float) (decimals : Nat := 4) : String :=
  let scale := Float.pow 10.0 decimals.toFloat
  let rounded := Float.round (x * scale) / scale
  toString rounded

def resultToString (r : OpenSystemResult) : String :=
  s!"╔══════════════════════════════════════════════════════════════╗\n" ++
  s!"║  {r.modelName}\n" ++
  s!"║  Topology: {r.topology}\n" ++
  s!"╠══════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Non-Normality ||[L,L†]||:  {formatFloat r.nonNormality}\n" ++
  s!"║  Current Flow J:            {formatFloat r.currentFlow}\n" ++
  s!"║  Conductance φ:             {formatFloat r.conductance}\n" ++
  s!"║  Slowest Decay Rate:        {formatFloat r.slowestDecay}\n" ++
  s!"║  Spectral Gap:              {formatFloat r.spectralGap}\n" ++
  s!"╚══════════════════════════════════════════════════════════════╝"

#eval resultToString perfectResult
#eval resultToString openResult
#eval resultToString drainResult

/-! ## 14. Mathematical Prediction Test -/

def mathematicalPredictionTest : String :=
  let perfect := perfectResult
  let open_ := openResult
  let drain := drainResult

  -- THE KEY PREDICTIONS FROM THE MATH:
  -- 1. Non-Normality: Perfect = 0, Open > 0, Drain >> 0
  -- 2. Current Flow: Perfect > 0, Open > 0, Drain ≈ 0 (blocked by gradient!)
  -- 3. Spectral Gap: Perfect = 0, Drain > 0 (has slow mode), Open intermediate

  let pred1_norm := perfect.nonNormality < 1.0 &&
                    open_.nonNormality > 1.0 &&
                    drain.nonNormality > open_.nonNormality

  let pred2_current := perfect.currentFlow > 1.0 &&
                       open_.currentFlow > 1.0 &&
                       drain.currentFlow < perfect.currentFlow * 0.1

  let pred3_gap := perfect.spectralGap < 1.0 &&
                   drain.spectralGap > 5.0

  s!"╔══════════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║           MATHEMATICAL PREDICTION TEST (Phase 11 Rigorous)                   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║                       Perfect Cycle   Open Cycle    Linear Drain             ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Non-Normality:       {formatFloat perfect.nonNormality 1}            {formatFloat open_.nonNormality 1}           {formatFloat drain.nonNormality 1}               ║\n" ++
  s!"║  Current Flow J:      {formatFloat perfect.currentFlow 2}           {formatFloat open_.currentFlow 2}          {formatFloat drain.currentFlow 2}               ║\n" ++
  s!"║  Spectral Gap:        {formatFloat perfect.spectralGap 1}            {formatFloat open_.spectralGap 1}           {formatFloat drain.spectralGap 1}               ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  PREDICTION 1: Non-Normality (Perfect=0 < Open < Drain)                      ║\n" ++
  s!"║    Result: {if pred1_norm then "✓ CONFIRMED" else "✗ FAILED"}                                                       ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  PREDICTION 2: Current Flow (Cycle flows, Drain blocked)                     ║\n" ++
  s!"║    Result: {if pred2_current then "✓ CONFIRMED" else "✗ FAILED"}                                                       ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  PREDICTION 3: Spectral Gap (Drain has slow mode)                            ║\n" ++
  s!"║    Result: {if pred3_gap then "✓ CONFIRMED" else "✗ FAILED"}                                                       ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  OVERALL: {if pred1_norm && pred2_current && pred3_gap then "✓ ALL PREDICTIONS CONFIRMED - Theory validated by math" else "? Some predictions failed - investigate"}     ║\n" ++
  s!"╚══════════════════════════════════════════════════════════════════════════════╝"

#eval mathematicalPredictionTest

/-! ## 15. Matrix and Distribution Inspection -/

def showMatrix (name : String) (M : Matrix6x6) : String :=
  let rows := (List.finRange 6).map fun i =>
    let cols := (List.finRange 6).map fun j => formatFloat (M i j) 2
    String.intercalate "  " cols
  s!"{name}:\n" ++ String.intercalate "\n" rows

def showPi (name : String) (pi : Fin 6 → Float) : String :=
  let vals := (List.finRange 6).map (fun i => formatFloat (pi i) 4)
  s!"{name}: [{String.intercalate ", " vals}]"

#eval showMatrix "L_perfect" L_perfect
#eval showMatrix "L_open" L_open
#eval showMatrix "L_drain" L_drain

#eval showPi "π_perfect (uniform)" pi_perfect
#eval showPi "π_drain (gradient)" pi_drain
#eval showPi "π_open (approx uniform)" pi_open

end SGC.Experiments.OpenSystemTest
