# C. elegans Pharyngeal Connectome Data

## Source

**Cook SJ, Crouse CM, Yemini E, Hall DH, Emmons SW, Hobert O.**
"The connectome of the Caenorhabditis elegans pharynx"
*J Comp Neurol.* 2020; 528: 2767-2784

- **DOI**: [10.1002/cne.24932](https://doi.org/10.1002/cne.24932)
- **Upstream file**: `cne24932-sup-0004-supinfo4.csv` (Supplementary Table 4)
- **Repository**: [OpenWorm ConnectomeToolbox](https://github.com/openworm/ConnectomeToolbox)
- **Direct link**: https://github.com/openworm/ConnectomeToolbox/blob/main/cect/data/cne24932-sup-0004-supinfo4.csv

## Files

| File | Description |
|------|-------------|
| `cook2020_pharynx_synapses.csv` | Raw CSV downloaded from OpenWorm (2024-01-30) |
| `extract_adjacency.py` | Python script to parse CSV and generate Lean code |
| `pharynx_adjacency.csv` | Extracted 20×20 adjacency matrix |

## Neuron Ordering (Fin 20 mapping)

The following 20 neurons from the pharyngeal nervous system are included:

| Index | Name | Class | Description |
|-------|------|-------|-------------|
| 0 | I1L | Interneuron | Left I1 interneuron |
| 1 | I1R | Interneuron | Right I1 interneuron |
| 2 | I2L | Interneuron | Left I2 interneuron |
| 3 | I2R | Interneuron | Right I2 interneuron |
| 4 | I3 | Interneuron | Unpaired I3 interneuron |
| 5 | I4 | Interneuron | Unpaired I4 interneuron |
| 6 | I5 | Interneuron | Unpaired I5 interneuron |
| 7 | I6 | Interneuron | Unpaired I6 interneuron |
| 8 | M1 | Motor | Unpaired M1 motor neuron |
| 9 | M2L | Motor | Left M2 motor neuron |
| 10 | M2R | Motor | Right M2 motor neuron |
| 11 | M3L | Motor | Left M3 motor neuron |
| 12 | M3R | Motor | Right M3 motor neuron |
| 13 | M4 | Motor | Unpaired M4 motor neuron |
| 14 | M5 | Motor | Unpaired M5 motor neuron |
| 15 | MCL | Marginal cell | Left marginal cell (pacemaker) |
| 16 | MCR | Marginal cell | Right marginal cell (pacemaker) |
| 17 | MI | Motor-interneuron | Motor-interneuron hybrid |
| 18 | NSML | Neurosecretory | Left NSM neurosecretory motor |
| 19 | NSMR | Neurosecretory | Right NSM neurosecretory motor |

## Extraction Methodology

1. **Input**: `cook2020_pharynx_synapses.csv` contains synapse counts between pharyngeal neurons
2. **Filtering**: Only connections between the 20 neurons listed above are included
3. **Weights**: Values represent chemical synapse counts; 0.5 values are averaged half-counts
4. **Output**: `adjacencyMatrix` in Lean where `A(i,j)` = synapse count from neuron `i` to neuron `j`

Run extraction:
```bash
python extract_adjacency.py
```

## Statistics

- **Neurons**: 20
- **Directed edges** (weight > 0): 161
- **Total synapse weight**: ~850.0
- **Self-loops**: 3 (M4→M4: 31.0, M5→M5: 1.0, NSML→NSML: 0.5)

## Notes

- MCL and MCR have no outgoing synapses to other neurons in this dataset
- The adjacency matrix is directed (asymmetric)
- Gap junctions are not included (chemical synapses only)
