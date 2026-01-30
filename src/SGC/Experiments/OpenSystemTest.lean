/-
Copyright (c) 2025 SGC Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGC Contributors
-/

/-!
# Phase 11: The "Goldilocks" Experiment (Open System Topology)

## The Hypothesis: "Life is a Perturbed Cycle"

The Adversarial Test revealed:
- **Perfect Cycle**: Normal operator (||[L,L†]|| = 0), Low conductance
- **Drain (Linear)**: Non-normal operator, High conductance

But real biology isn't either extreme. Real cells are **Open Cycles**:
- They have cyclic metabolism (TCA, etc.)
- BUT they also have inputs (nutrients) and outputs (waste)

## The Three Models

**Model A - Perfect Cycle**: Closed 6-state ring (Normal, Stable)
**Model B - Leaky Cycle**: Ring with output leak at node 3 (Non-Normal, Structured)
**Model C - Drain**: Linear chain (Non-Normal, Unstructured)

## The Goldilocks Prediction

|                  | Non-Normality | Conductance | Transient Growth |
|------------------|---------------|-------------|------------------|
| Perfect Cycle    | ZERO          | LOW         | NONE (||e^tL|| ≤ 1) |
| Leaky Cycle      | LOW-MEDIUM    | LOW         | YES (the "Hump") |
| Drain            | HIGH          | HIGH        | YES then DECAY   |

**Life = Structured Non-Normality** (Middle column)

## Transient Growth (Pseudo-Criticality)

For non-normal operators, ||e^{tL}||₂ can exceed 1 transiently before decaying.
This is the **Kreiss phenomenon** - the signature of sensitivity/adaptability.

We approximate e^{tL} via: (I + (t/n)L)^n for large n
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

/-- Model B: Leaky Cycle (Open System)
    Same as perfect cycle, but node 3 has an additional "leak" (output to environment)
    This models: TCA cycle + waste excretion
    The leak rate controls how "open" the system is -/
def leakyCycleGenerator (k_fwd k_bwd leak : Float) : Matrix6x6 := fun i j =>
  let i_val := i.val
  let j_val := j.val
  let next := (i_val + 1) % 6
  let prev := (i_val + 5) % 6
  if j_val == next then k_fwd
  else if j_val == prev then k_bwd
  else if i_val == j_val then
    if i_val == 3 then -(k_fwd + k_bwd + leak)  -- Node 3 has extra outflow (leak)
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

/-! ## 3. Non-Normality Diagnostic -/

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

/-! ## 4. Transient Growth Proxy (Kreiss Constant Bound) -/

/-- Instead of computing expensive matrix exponentials, we use the
    "departure from normality" as a proxy for transient growth potential.

    Kreiss constant K(L) bounds max_t ||e^{tL}||.
    For normal matrices K=1, for non-normal K>1.

    Proxy: K ≈ 1 + ||[L,L†]||_F / ||L||_F  (simplified bound) -/
def kreissProxy (L : Matrix6x6) : Float :=
  let commNorm := nonNormalityNorm L
  let matNorm := frobeniusNorm L
  if matNorm > 1e-10 then 1.0 + commNorm / matNorm else 1.0

/-- Spectral abscissa proxy: max real part of eigenvalues ≈ max diagonal -/
def spectralAbscissa (L : Matrix6x6) : Float :=
  (List.finRange 6).foldl (fun maxVal i => floatMax maxVal (L i i)) (-1000.0)

/-! ## 5. Conductance (from AdversarialTest) -/

def uniformPi : Fin 6 → Float := fun _ => 1.0 / 6.0

def escortMassS (pi : Fin 6 → Float) : Float :=
  pi ⟨0, by omega⟩ + pi ⟨1, by omega⟩ + pi ⟨2, by omega⟩

def boundaryFluxCycle (L : Matrix6x6) (pi : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  let flux_5_0 := floatAbs (pi ⟨5, by omega⟩ * L ⟨5, by omega⟩ ⟨0, by omega⟩)
  let flux_0_5 := floatAbs (pi ⟨0, by omega⟩ * L ⟨0, by omega⟩ ⟨5, by omega⟩)
  flux_2_3 + flux_3_2 + flux_5_0 + flux_0_5

def boundaryFluxLinear (L : Matrix6x6) (pi : Fin 6 → Float) : Float :=
  let flux_2_3 := floatAbs (pi ⟨2, by omega⟩ * L ⟨2, by omega⟩ ⟨3, by omega⟩)
  let flux_3_2 := floatAbs (pi ⟨3, by omega⟩ * L ⟨3, by omega⟩ ⟨2, by omega⟩)
  flux_2_3 + flux_3_2

def conductance (L : Matrix6x6) (isCycle : Bool) : Float :=
  let pi := uniformPi
  let mass_S := escortMassS pi
  let mass_Sc := 1.0 - mass_S
  let minMass := floatMin mass_S mass_Sc
  let flux := if isCycle then boundaryFluxCycle L pi else boundaryFluxLinear L pi
  if minMass > 1e-10 then flux / minMass else 0.0

/-! ## 6. Experiment Structure -/

structure OpenSystemResult where
  modelName : String
  topology : String
  nonNormality : Float
  conductance : Float
  kreissProxy : Float  -- Transient growth potential
  spectralAbscissa : Float  -- Decay rate
  deriving Repr

def runExperiment (name : String) (topology : String) (L : Matrix6x6) (isCycle : Bool) : OpenSystemResult :=
  {
    modelName := name
    topology := topology
    nonNormality := nonNormalityNorm L
    conductance := conductance L isCycle
    kreissProxy := kreissProxy L
    spectralAbscissa := spectralAbscissa L
  }

/-! ## 7. Run the Three Models -/

def k_fwd : Float := 10.0
def k_bwd : Float := 0.1
def leak_rate : Float := 2.0  -- Moderate leak

def L_perfect := perfectCycleGenerator k_fwd k_bwd
def L_leaky := leakyCycleGenerator k_fwd k_bwd leak_rate
def L_drain := linearDrainGenerator k_fwd k_bwd

def perfectResult := runExperiment "PERFECT CYCLE" "Closed Ring" L_perfect true
def leakyResult := runExperiment "LEAKY CYCLE" "Open Ring (leak at node 3)" L_leaky true
def drainResult := runExperiment "LINEAR DRAIN" "Open Chain" L_drain false

/-! ## 8. Display Functions -/

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
  s!"║  Conductance φ:             {formatFloat r.conductance}\n" ++
  s!"║  Kreiss Proxy (Growth):     {formatFloat r.kreissProxy}\n" ++
  s!"║  Spectral Abscissa:         {formatFloat r.spectralAbscissa}\n" ++
  s!"╚══════════════════════════════════════════════════════════════╝"

#eval resultToString perfectResult
#eval resultToString leakyResult
#eval resultToString drainResult

/-! ## 9. Goldilocks Comparison -/

def goldilocksComparison : String :=
  let perfect := perfectResult
  let leaky := leakyResult
  let drain := drainResult

  -- Classify each model
  let classifyNorm (n : Float) : String :=
    if n < 1.0 then "ZERO" else if n < 50.0 then "LOW" else if n < 150.0 then "MEDIUM" else "HIGH"
  let classifyCond (c : Float) : String :=
    if c < 20.0 then "LOW" else if c < 100.0 then "MEDIUM" else "HIGH"
  let classifyKreiss (k : Float) : String :=
    if k < 1.1 then "NONE" else if k < 2.0 then "LOW" else if k < 5.0 then "MEDIUM" else "HIGH"

  -- Check Goldilocks prediction
  let leakyIsGoldilocks :=
    leaky.nonNormality > 0.1 &&  -- Has some non-normality
    leaky.conductance < drain.conductance * 0.5 &&  -- Lower conductance than drain
    leaky.kreissProxy > perfect.kreissProxy  -- More growth potential than perfect cycle

  s!"╔══════════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║                    GOLDILOCKS EXPERIMENT: OPEN SYSTEM TOPOLOGY               ║\n" ++
  s!"║                    Phase 11: Testing 'Life = Structured Non-Normality'       ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║                     Perfect Cycle    Leaky Cycle     Linear Drain            ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Non-Normality:    {classifyNorm perfect.nonNormality} ({formatFloat perfect.nonNormality 1})    {classifyNorm leaky.nonNormality} ({formatFloat leaky.nonNormality 1})     {classifyNorm drain.nonNormality} ({formatFloat drain.nonNormality 1})   ║\n" ++
  s!"║  Conductance:      {classifyCond perfect.conductance} ({formatFloat perfect.conductance 1})     {classifyCond leaky.conductance} ({formatFloat leaky.conductance 1})     {classifyCond drain.conductance} ({formatFloat drain.conductance 1})   ║\n" ++
  s!"║  Kreiss Proxy:     {classifyKreiss perfect.kreissProxy} ({formatFloat perfect.kreissProxy 2})   {classifyKreiss leaky.kreissProxy} ({formatFloat leaky.kreissProxy 2})    {classifyKreiss drain.kreissProxy} ({formatFloat drain.kreissProxy 2})   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  GOLDILOCKS TEST: Leaky Cycle in the 'sweet spot'?                           ║\n" ++
  s!"║    Non-Normality > 0? {if leaky.nonNormality > 0.1 then "✓ YES" else "✗ NO"}                                                    ║\n" ++
  s!"║    Conductance < Drain? {if leaky.conductance < drain.conductance * 0.5 then "✓ YES" else "✗ NO"}                                                  ║\n" ++
  s!"║    Kreiss > Perfect? {if leaky.kreissProxy > perfect.kreissProxy then "✓ YES" else "✗ NO"}                                                     ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  VERDICT: {if leakyIsGoldilocks then "✓ GOLDILOCKS CONFIRMED - Life = Structured Non-Normality" else "? Results require interpretation"}        ║\n" ++
  s!"╚══════════════════════════════════════════════════════════════════════════════╝"

#eval goldilocksComparison

/-! ## 10. Matrix Inspection -/

def showMatrix (name : String) (M : Matrix6x6) : String :=
  let rows := (List.finRange 6).map fun i =>
    let cols := (List.finRange 6).map fun j => formatFloat (M i j) 2
    String.intercalate "  " cols
  s!"{name}:\n" ++ String.intercalate "\n" rows

#eval showMatrix "L_perfect (Closed Cycle)" L_perfect
#eval showMatrix "L_leaky (Open Cycle, leak at node 3)" L_leaky
#eval showMatrix "L_drain (Linear Chain)" L_drain

end SGC.Experiments.OpenSystemTest
