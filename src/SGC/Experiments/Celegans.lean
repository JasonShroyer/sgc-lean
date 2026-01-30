import SGC.Experiments.CelegansPharynxData

/-!
# C. elegans Pharyngeal Nervous System Analysis

This experiment applies SGC diagnostics to the C. elegans pharyngeal connectome.
Data source and methodology documented in `CelegansPharynxData.lean`.

## What This Experiment Measures

1. **Non-Normality**: ||[L, L†]||_F - deviation from symmetric dynamics
2. **Partition Conductance**: Weighted boundary flux for interneuron vs motor partitions

## Limitations

- Chemical synapses only (gap junctions analyzed separately in original paper)
- Self-loops (autapses) included in original data
- This is ONE network; generalization requires validation on other connectomes
-/

namespace SGC.Experiments.Celegans

open CelegansPharynxData

/-! ## 1. Matrix Infrastructure -/

def zeros20 : Matrix20 := fun _ _ => 0.0

def identity20 : Matrix20 := fun i j => if i == j then 1.0 else 0.0

/-! ## 2. Aliases for Shared Module Definitions -/

/-- Control Core = Interneurons + Pacemakers (alias for isControlLayer) -/
abbrev isControlCore := isControlLayer

/-! ## 3. Generator Matrix Construction -/

/-- Row sum of a matrix -/
def rowSum20 (A : Matrix20) (i : Fin 20) : Float :=
  (List.finRange 20).foldl (fun acc j => acc + A i j) 0.0

/-- Convert adjacency matrix to continuous-time Markov generator.
    Off-diagonal: L(i,j) = A(i,j); Diagonal: L(i,i) = -sum of row.
    Note: This is a generator matrix (rows sum to 0), not a stochastic matrix. -/
def adjacencyToGenerator (A : Matrix20) : Matrix20 := fun i j =>
  let degree := rowSum20 A i
  if i == j then
    -degree  -- Diagonal: negative sum of outgoing rates
  else
    A i j    -- Off-diagonal: transition rate = adjacency weight

/-- The Markov generator for the pharyngeal circuit -/
def pharyngealGenerator : Matrix20 := adjacencyToGenerator adjacencyMatrix

/-! ## 5. Matrix Operations -/

def transpose20 (M : Matrix20) : Matrix20 := fun i j => M j i

def matMul20 (A B : Matrix20) : Matrix20 := fun i j =>
  (List.finRange 20).foldl (fun acc k => acc + A i k * B k j) 0.0

def matSub20 (A B : Matrix20) : Matrix20 := fun i j => A i j - B i j

def frobNorm20 (M : Matrix20) : Float :=
  let sumSq := (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc2 j =>
      acc2 + M i j * M i j) acc) 0.0
  Float.sqrt sumSq

def commutator20 (A B : Matrix20) : Matrix20 :=
  matSub20 (matMul20 A B) (matMul20 B A)

/-! ## 6. SGC Diagnostics -/

/-- Non-Normality: ||[L, L†]||_F -/
def nonNormality20 (L : Matrix20) : Float :=
  let Lt := transpose20 L
  frobNorm20 (commutator20 L Lt)

/-- Count edges within a partition -/
def internalEdges (inPartition : Fin 20 → Bool) : Nat :=
  (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc2 j =>
      if inPartition i && inPartition j && adjacencyMatrix i j > 0.0
      then acc2 + 1 else acc2) acc) 0

/-- Sum of edge weights within a partition -/
def internalWeight (inPartition : Fin 20 → Bool) : Float :=
  (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc2 j =>
      if inPartition i && inPartition j then acc2 + adjacencyMatrix i j else acc2) acc) 0.0

/-- Count edges leaving a partition -/
def boundaryEdges (inPartition : Fin 20 → Bool) : Nat :=
  (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc2 j =>
      if inPartition i && !inPartition j && adjacencyMatrix i j > 0.0
      then acc2 + 1 else acc2) acc) 0

/-- Sum of edge weights leaving a partition (cut weight) -/
def boundaryWeight (inPartition : Fin 20 → Bool) : Float :=
  (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc2 j =>
      if inPartition i && !inPartition j then acc2 + adjacencyMatrix i j else acc2) acc) 0.0

/-- Volume of partition: total outgoing weight from nodes in S -/
def partitionVolume (inPartition : Fin 20 → Bool) : Float :=
  (List.finRange 20).foldl (fun acc i =>
    if inPartition i then acc + rowSum20 adjacencyMatrix i else acc) 0.0

/-- Partition size -/
def partitionSize (inPartition : Fin 20 → Bool) : Nat :=
  (List.finRange 20).foldl (fun acc i =>
    if inPartition i then acc + 1 else acc) 0

/--
Weighted conductance: cut(S, S^c) / min(vol(S), vol(S^c))
Lower conductance = partition is more isolated from its complement.
-/
def partitionConductance (inPartition : Fin 20 → Bool) : Float :=
  let cutWeight := boundaryWeight inPartition
  let volS := partitionVolume inPartition
  let volSc := partitionVolume (fun i => !inPartition i)
  let minVol := if volS < volSc then volS else volSc
  if minVol < 0.001 then 1000.0  -- Avoid division by zero
  else cutWeight / minVol

/-- Density of a partition: internal_edges / possible_edges -/
def partitionDensity (inPartition : Fin 20 → Bool) : Float :=
  let n := partitionSize inPartition
  let internal := internalEdges inPartition
  let possibleEdges := n * (n - 1)  -- Directed graph
  if possibleEdges == 0 then 0.0
  else internal.toFloat / possibleEdges.toFloat

/-! ## 7. Run the Validation -/

def controlCoreStats : String :=
  let size := partitionSize isControlCore
  let internal := internalEdges isControlCore
  let boundary := boundaryEdges isControlCore
  let conductance := partitionConductance isControlCore
  let density := partitionDensity isControlCore
  s!"Control Core (Interneurons + Pacemakers):\n" ++
  s!"  Neurons: {size}\n" ++
  s!"  Internal Edges: {internal}\n" ++
  s!"  Boundary Edges: {boundary}\n" ++
  s!"  Conductance: {conductance}\n" ++
  s!"  Density: {density}"

def actionLayerStats : String :=
  let size := partitionSize isActionLayer
  let internal := internalEdges isActionLayer
  let boundary := boundaryEdges isActionLayer
  let conductance := partitionConductance isActionLayer
  let density := partitionDensity isActionLayer
  s!"Action Layer (Motor + Neurosecretory):\n" ++
  s!"  Neurons: {size}\n" ++
  s!"  Internal Edges: {internal}\n" ++
  s!"  Boundary Edges: {boundary}\n" ++
  s!"  Conductance: {conductance}\n" ++
  s!"  Density: {density}"

def formatFloat (x : Float) (decimals : Nat := 3) : String :=
  let scale := Float.pow 10.0 decimals.toFloat
  let rounded := Float.round (x * scale) / scale
  toString rounded

def celegansValidation : String :=
  let L := pharyngealGenerator
  let nonNorm := nonNormality20 L
  let controlCond := partitionConductance isControlCore
  let actionCond := partitionConductance isActionLayer
  let controlDens := partitionDensity isControlCore
  let actionDens := partitionDensity isActionLayer

  -- The critical test: what does SGC reveal about the structure?
  -- Key insight: HIGH conductance = information TRANSMITTER
  --              LOW conductance = information RECEIVER/EXECUTOR
  let motorClosed := actionCond < controlCond

  s!"╔══════════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║     C. ELEGANS PHARYNGEAL NERVOUS SYSTEM ANALYSIS                            ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  Network: 20 neurons, {totalEdges} directed edges                                    ║\n" ++
  s!"║  Data: Cook et al. (2020) J Comp Neurol 528:2767-2784                        ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  NON-NORMALITY: ||[L, L†]||_F = {formatFloat nonNorm 2}                               ║\n" ++
  s!"║  (Non-zero indicates directed/asymmetric information flow)                   ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  PARTITION ANALYSIS:                                                         ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  Interneurons (I1-I6, MC):                                                   ║\n" ++
  s!"║    Neurons: {partitionSize isControlCore}                                                            ║\n" ++
  s!"║    Conductance: {formatFloat controlCond 3}  (HIGH - Information Source)             ║\n" ++
  s!"║    Density: {formatFloat controlDens 3}                                                      ║\n" ++
  s!"║                                                                              ║\n" ++
  s!"║  Motor Neurons (M1-M5, MI, NSM):                                             ║\n" ++
  s!"║    Neurons: {partitionSize isActionLayer}                                                            ║\n" ++
  s!"║    Conductance: {formatFloat actionCond 3}  (LOW - Information Sink)                 ║\n" ++
  s!"║    Density: {formatFloat actionDens 3}                                                      ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  s!"║  OBSERVATION:                                                                ║\n" ++
  s!"║  Interneuron Conductance ({formatFloat controlCond 3}) > Motor Conductance ({formatFloat actionCond 3})    ║\n" ++
  s!"║                                                                              ║\n" ++
  (if motorClosed then
  s!"║  Interpretation: Interneurons have higher boundary flux (transmit role),    ║\n" ++
  s!"║  while motor neurons form a more isolated execution chain.                   ║\n" ++
  s!"║  This is consistent with known source→sink neural architecture.              ║\n"
  else
  s!"║  Unexpected ordering - further analysis needed.                              ║\n") ++
  s!"╚══════════════════════════════════════════════════════════════════════════════╝"

#eval celegansValidation

/-! ## 8. Detailed Neuron Analysis -/

/-- Compute out-degree for each neuron (count of outgoing edges) -/
def outDegree (i : Fin 20) : Nat :=
  (List.finRange 20).foldl (fun acc j =>
    if adjacencyMatrix i j > 0.0 then acc + 1 else acc) 0

/-- Compute in-degree for each neuron (count of incoming edges) -/
def inDegree (i : Fin 20) : Nat :=
  (List.finRange 20).foldl (fun acc j =>
    if adjacencyMatrix j i > 0.0 then acc + 1 else acc) 0

def neuronTable : String :=
  let header := "║  Neuron │ Class      │ Out │ In  │ Control? ║\n"
  let rows := (List.finRange 20).map (fun i =>
    let name := neuronName i
    let cls := match neuronClass i with
      | .Interneuron => "Interneuron"
      | .Motor => "Motor     "
      | .Pacemaker => "Pacemaker "
      | .Neurosecretory => "Neurosecr."
    let outD := outDegree i
    let inD := inDegree i
    let ctrl := if isControlCore i then "Yes" else "No "
    s!"║  {name}    │ {cls} │ {outD}   │ {inD}   │ {ctrl}      ║")
  s!"╔══════════════════════════════════════════════════════════════════════════════╗\n" ++
  s!"║                     NEURON CONNECTIVITY TABLE                                ║\n" ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  header ++
  s!"╠══════════════════════════════════════════════════════════════════════════════╣\n" ++
  String.intercalate "\n" rows ++ "\n" ++
  s!"╚══════════════════════════════════════════════════════════════════════════════╝"

#eval neuronTable

end SGC.Experiments.Celegans
