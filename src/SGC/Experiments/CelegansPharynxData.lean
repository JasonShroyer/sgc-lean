/-!
# C. elegans Pharyngeal Nervous System Connectome Data

## Data Source

**Cook SJ, Crouse CM, Yemini E, Hall DH, Emmons SW, Hobert O.**
"The connectome of the Caenorhabditis elegans pharynx"
*J Comp Neurol.* 2020; 528: 2767-2784
DOI: 10.1002/cne.24932

## Dataset Statistics

- **Neurons**: 20 (pharyngeal nervous system subset)
- **Connections**: 161 directed edges with non-zero weight
- **Weights**: Synapse counts (chemical synapses only)
- **Source file**: cne24932-sup-0004-supinfo4.csv (Supplementary Table 4)

## Neuron Ordering (Fin 20 → neuron name)

| Index | Name | Class |
|-------|------|-------|
| 0 | I1L | Interneuron |
| 1 | I1R | Interneuron |
| 2 | I2L | Interneuron |
| 3 | I2R | Interneuron |
| 4 | I3 | Interneuron |
| 5 | I4 | Interneuron |
| 6 | I5 | Interneuron |
| 7 | I6 | Interneuron |
| 8 | M1 | Motor |
| 9 | M2L | Motor |
| 10 | M2R | Motor |
| 11 | M3L | Motor |
| 12 | M3R | Motor |
| 13 | M4 | Motor |
| 14 | M5 | Motor |
| 15 | MCL | Marginal cell |
| 16 | MCR | Marginal cell |
| 17 | MI | Motor-interneuron |
| 18 | NSML | Neurosecretory |
| 19 | NSMR | Neurosecretory |

## Notes

- Weights of 0.5 represent averaged half-counts (e.g., from bilateral pairs)
- MCL and MCR have no outgoing synapses to other neurons in this dataset
- See `data/README.md` for extraction methodology
-/

namespace SGC.Experiments.CelegansPharynxData

/-! ## Type Definitions -/

abbrev Matrix20 := Fin 20 → Fin 20 → Float

/-! ## Neuron Names and Classifications -/

def neuronName (i : Fin 20) : String :=
  match i.val with
  | 0 => "I1L" | 1 => "I1R" | 2 => "I2L" | 3 => "I2R"
  | 4 => "I3"  | 5 => "I4"  | 6 => "I5"  | 7 => "I6"
  | 8 => "M1"  | 9 => "M2L" | 10 => "M2R"
  | 11 => "M3L" | 12 => "M3R" | 13 => "M4" | 14 => "M5"
  | 15 => "MCL" | 16 => "MCR" | 17 => "MI"
  | 18 => "NSML" | 19 => "NSMR" | _ => "?"

/-- Interneurons: I1L, I1R, I2L, I2R, I3, I4, I5, I6 -/
def isInterneuron (i : Fin 20) : Bool :=
  i.val < 8

/-- Motor neurons: M1-M5, MI -/
def isMotor (i : Fin 20) : Bool :=
  match i.val with
  | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 17 => true
  | _ => false

/-- Marginal cells (pacemaker): MCL, MCR -/
def isMarginalCell (i : Fin 20) : Bool :=
  i.val == 15 || i.val == 16

/-- Neurosecretory motor neurons: NSML, NSMR -/
def isNeurosecretory (i : Fin 20) : Bool :=
  i.val == 18 || i.val == 19

/-- Control layer: interneurons + marginal cells -/
def isControlLayer (i : Fin 20) : Bool :=
  isInterneuron i || isMarginalCell i

/-- Action layer: motor + neurosecretory -/
def isActionLayer (i : Fin 20) : Bool :=
  isMotor i || isNeurosecretory i

/-! ## Weighted Adjacency Matrix

A(i,j) = synapse count from neuron i to neuron j.
Data extracted from Cook et al. 2020 Supplementary Table 4.
-/

def adjacencyMatrix : Matrix20 := fun i j =>
  let w := fun (a b : Nat) (v : Float) => if i.val == a && j.val == b then v else 0.0
  -- Row 0: I1L
  w 0 2 13.0 + w 0 4 2.5 + w 0 6 4.5 + w 0 9 3.0 + w 0 11 11.0 + w 0 12 1.5 + w 0 15 2.0 + w 0 16 3.0 + w 0 17 2.0 + w 0 18 5.5 +
  -- Row 1: I1R
  w 1 2 1.0 + w 1 3 8.0 + w 1 4 7.0 + w 1 6 2.0 + w 1 8 3.0 + w 1 9 0.5 + w 1 10 3.5 + w 1 11 0.5 + w 1 12 6.0 + w 1 13 1.0 + w 1 15 4.0 + w 1 16 8.5 + w 1 17 1.0 + w 1 18 1.0 + w 1 19 3.5 +
  -- Row 2: I2L
  w 2 0 1.5 + w 2 3 4.0 + w 2 5 15.5 + w 2 6 2.0 + w 2 7 1.0 + w 2 8 1.5 + w 2 12 2.0 + w 2 13 2.0 + w 2 18 16.0 + w 2 19 25.0 +
  -- Row 3: I2R
  w 3 1 1.0 + w 3 2 3.0 + w 3 5 15.5 + w 3 6 4.0 + w 3 8 2.5 + w 3 10 1.5 + w 3 13 1.0 + w 3 15 0.5 + w 3 18 32.5 + w 3 19 8.5 +
  -- Row 4: I3
  w 4 0 0.5 + w 4 1 0.5 + w 4 6 2.5 + w 4 8 1.5 + w 4 9 1.5 + w 4 10 0.5 + w 4 11 2.0 + w 4 12 3.0 + w 4 13 2.0 + w 4 15 2.5 + w 4 16 2.5 + w 4 17 1.5 + w 4 19 1.5 +
  -- Row 5: I4
  w 5 3 7.0 + w 5 6 2.0 + w 5 9 5.0 + w 5 10 2.0 + w 5 11 6.5 + w 5 12 23.5 + w 5 17 1.0 + w 5 18 8.5 + w 5 19 15.5 +
  -- Row 6: I5
  w 6 0 1.5 + w 6 1 2.0 + w 6 2 3.5 + w 6 3 3.0 + w 6 4 10.5 + w 6 5 7.0 + w 6 8 3.0 + w 6 9 5.0 + w 6 10 1.0 + w 6 11 12.5 + w 6 12 2.0 + w 6 13 26.5 + w 6 14 2.0 + w 6 16 3.5 + w 6 17 7.5 + w 6 18 5.0 + w 6 19 20.5 +
  -- Row 7: I6
  w 7 2 2.0 + w 7 13 12.5 + w 7 18 21.0 + w 7 19 4.0 +
  -- Row 8: M1
  w 8 1 1.0 + w 8 2 3.0 + w 8 3 3.5 + w 8 4 8.0 + w 8 5 0.5 + w 8 6 2.5 + w 8 13 1.0 + w 8 14 1.0 + w 8 17 7.5 + w 8 18 5.0 +
  -- Row 9: M2L
  w 9 2 1.0 + w 9 4 1.5 + w 9 5 8.0 + w 9 6 2.0 + w 9 11 3.0 + w 9 12 0.5 + w 9 15 1.0 +
  -- Row 10: M2R
  w 10 3 1.0 + w 10 5 1.0 + w 10 6 3.0 + w 10 9 1.0 + w 10 11 2.0 + w 10 12 3.0 + w 10 16 9.0 + w 10 17 5.0 + w 10 19 1.0 +
  -- Row 11: M3L
  w 11 12 1.0 + w 11 15 0.5 + w 11 17 0.5 + w 11 18 1.0 +
  -- Row 12: M3R
  w 12 0 3.0 + w 12 13 2.0 + w 12 15 1.0 + w 12 17 3.0 +
  -- Row 13: M4
  w 13 2 0.5 + w 13 5 5.5 + w 13 6 1.5 + w 13 7 5.0 + w 13 9 2.0 + w 13 11 1.0 + w 13 13 31.0 + w 13 15 0.5 +
  -- Row 14: M5
  w 14 6 4.0 + w 14 8 1.0 + w 14 13 2.0 + w 14 14 1.0 +
  -- Row 15: MCL (no outgoing neuron-to-neuron synapses)
  -- Row 16: MCR (no outgoing neuron-to-neuron synapses)
  -- Row 17: MI
  w 17 0 0.5 + w 17 4 1.5 + w 17 5 1.0 + w 17 8 7.0 + w 17 9 3.5 + w 17 10 2.0 + w 17 11 5.5 + w 17 12 2.0 + w 17 15 2.5 + w 17 18 2.0 + w 17 19 1.5 +
  -- Row 18: NSML
  w 18 2 0.5 + w 18 3 0.5 + w 18 5 2.0 + w 18 6 0.5 + w 18 11 20.5 + w 18 12 0.5 + w 18 13 12.5 + w 18 18 0.5 + w 18 19 7.0 +
  -- Row 19: NSMR
  w 19 2 1.0 + w 19 3 2.0 + w 19 5 2.5 + w 19 7 2.0 + w 19 11 1.0 + w 19 12 22.5 + w 19 18 2.0

/-! ## Derived Statistics (computed from matrix) -/

/-- Count non-zero edges (weight > 0) -/
def totalEdges : Nat :=
  (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc' j =>
      if adjacencyMatrix i j > 0.0 then acc' + 1 else acc') acc) 0

/-- Total weight of all edges -/
def totalWeight : Float :=
  (List.finRange 20).foldl (fun acc i =>
    (List.finRange 20).foldl (fun acc' j =>
      acc' + adjacencyMatrix i j) acc) 0.0

/-- Out-degree (count of outgoing edges) for neuron i -/
def outDegree (i : Fin 20) : Nat :=
  (List.finRange 20).foldl (fun acc j =>
    if adjacencyMatrix i j > 0.0 then acc + 1 else acc) 0

/-- In-degree (count of incoming edges) for neuron i -/
def inDegree (i : Fin 20) : Nat :=
  (List.finRange 20).foldl (fun acc j =>
    if adjacencyMatrix j i > 0.0 then acc + 1 else acc) 0

/-- Weighted out-degree (sum of outgoing weights) for neuron i -/
def weightedOutDegree (i : Fin 20) : Float :=
  (List.finRange 20).foldl (fun acc j => acc + adjacencyMatrix i j) 0.0

/-- Weighted in-degree (sum of incoming weights) for neuron i -/
def weightedInDegree (i : Fin 20) : Float :=
  (List.finRange 20).foldl (fun acc j => acc + adjacencyMatrix j i) 0.0

/-! ## Generator Matrix Construction

Convert adjacency to continuous-time Markov generator:
- Off-diagonal: L(i,j) = A(i,j) for i ≠ j
- Diagonal: L(i,i) = -∑_{j≠i} A(i,j)

This ensures row sums equal zero (probability conservation).
Note: This is a generator matrix, NOT a row-stochastic transition matrix.
-/

def adjacencyToGenerator : Matrix20 := fun i j =>
  if i == j then
    let rowSum := (List.finRange 20).foldl (fun acc k =>
      if k != i then acc + adjacencyMatrix i k else acc) 0.0
    (0.0 - rowSum)
  else
    adjacencyMatrix i j

end SGC.Experiments.CelegansPharynxData
