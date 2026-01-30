#!/usr/bin/env python3
"""
Extract neuron-to-neuron adjacency matrix from Cook et al. 2020 pharynx data.

Source: Cook SJ, Crouse CM, Yemini E, Hall DH, Emmons SW, Hobert O.
        "The connectome of the Caenorhabditis elegans pharynx"
        J Comp Neurol. 2020; 528: 2767-2784
        DOI: 10.1002/cne.24932

Data: cne24932-sup-0004-supinfo4.csv (from OpenWorm ConnectomeToolbox)
"""

import csv
from collections import defaultdict

# The 20 pharyngeal neurons (excluding RIPL, RIPR which are ring interneurons)
PHARYNGEAL_NEURONS = [
    'I1L', 'I1R', 'I2L', 'I2R', 'I3', 'I4', 'I5', 'I6',  # Interneurons (8)
    'M1', 'M2L', 'M2R', 'M3L', 'M3R', 'M4', 'M5',        # Motor neurons (7)
    'MCL', 'MCR',                                         # Marginal cells (2)
    'MI',                                                 # Motor-interneuron (1)
    'NSML', 'NSMR'                                        # Neurosecretory (2)
]

# Classification
INTERNEURONS = {'I1L', 'I1R', 'I2L', 'I2R', 'I3', 'I4', 'I5', 'I6'}
MOTOR_NEURONS = {'M1', 'M2L', 'M2R', 'M3L', 'M3R', 'M4', 'M5', 'MI'}
PACEMAKERS = {'MCL', 'MCR'}
NEUROSECRETORY = {'NSML', 'NSMR'}

def load_data(filename):
    """Load CSV and extract neuron-to-neuron connections."""
    connections = defaultdict(float)
    
    with open(filename, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            source = row['Source'].strip()
            target = row['Target'].strip()
            weight = float(row['Weight'])
            
            # Only keep neuron-to-neuron connections
            if source in PHARYNGEAL_NEURONS and target in PHARYNGEAL_NEURONS:
                # Aggregate weights for duplicate edges
                connections[(source, target)] += weight
    
    return connections

def generate_adjacency_matrix(connections):
    """Generate adjacency matrix in Lean-compatible format."""
    n = len(PHARYNGEAL_NEURONS)
    idx = {neuron: i for i, neuron in enumerate(PHARYNGEAL_NEURONS)}
    
    # Build matrix
    matrix = [[0.0] * n for _ in range(n)]
    for (src, tgt), weight in connections.items():
        i, j = idx[src], idx[tgt]
        matrix[i][j] = weight
    
    return matrix

def print_lean_code(matrix, connections):
    """Print Lean4 code for the adjacency matrix."""
    n = len(PHARYNGEAL_NEURONS)
    
    print("/-!")
    print("# Cook et al. 2020 Pharyngeal Connectome Data")
    print()
    print("Source: Cook SJ, Crouse CM, Yemini E, Hall DH, Emmons SW, Hobert O.")
    print('        "The connectome of the Caenorhabditis elegans pharynx"')
    print("        J Comp Neurol. 2020; 528: 2767-2784")
    print("        DOI: 10.1002/cne.24932")
    print()
    print("Data extracted from supplementary file cne24932-sup-0004-supinfo4.csv")
    print("Available at: https://github.com/openworm/ConnectomeToolbox/")
    print("-/")
    print()
    
    print("-- Neuron indices (0-19)")
    for i, neuron in enumerate(PHARYNGEAL_NEURONS):
        cls = "Interneuron" if neuron in INTERNEURONS else \
              "Motor" if neuron in MOTOR_NEURONS else \
              "Pacemaker" if neuron in PACEMAKERS else "Neurosecretory"
        print(f"-- {i:2d}: {neuron:5s} ({cls})")
    print()
    
    print("/-- Adjacency matrix with synapse counts (weighted)")
    print("    Row = source, Column = target -/")
    print("def adjacencyMatrix : Matrix20 := fun i j =>")
    print("  let w := fun (a b : Nat) (v : Float) => if i.val == a && j.val == b then v else 0.0")
    
    # Generate non-zero entries
    entries = []
    for i in range(n):
        for j in range(n):
            if matrix[i][j] > 0:
                entries.append((i, j, matrix[i][j]))
    
    if entries:
        print("  " + " + ".join([f"w {i} {j} {v}" for i, j, v in entries]))
    else:
        print("  0.0")
    
    print()
    print(f"-- Total neuron-to-neuron connections: {len(connections)}")
    print(f"-- Total synapse weight: {sum(connections.values()):.1f}")

def print_edge_list(connections):
    """Print edge list for verification."""
    print("\n-- Edge list (source -> target : weight)")
    for (src, tgt), weight in sorted(connections.items()):
        print(f"-- {src} -> {tgt} : {weight}")

def print_csv_adjacency(matrix):
    """Print CSV format adjacency matrix."""
    print("\n# Adjacency Matrix (CSV format)")
    print("# Rows/Cols: " + ",".join(PHARYNGEAL_NEURONS))
    print(",".join(PHARYNGEAL_NEURONS))
    for i, row in enumerate(matrix):
        print(",".join([f"{v:.1f}" for v in row]))

def main():
    connections = load_data('cook2020_pharynx_synapses.csv')
    matrix = generate_adjacency_matrix(connections)
    
    print("=" * 70)
    print("COOK ET AL. 2020 - PHARYNGEAL CONNECTOME ANALYSIS")
    print("=" * 70)
    print(f"\nNeurons: {len(PHARYNGEAL_NEURONS)}")
    print(f"  Interneurons: {len(INTERNEURONS)} ({', '.join(sorted(INTERNEURONS))})")
    print(f"  Motor: {len(MOTOR_NEURONS)} ({', '.join(sorted(MOTOR_NEURONS))})")
    print(f"  Pacemaker: {len(PACEMAKERS)} ({', '.join(sorted(PACEMAKERS))})")
    print(f"  Neurosecretory: {len(NEUROSECRETORY)} ({', '.join(sorted(NEUROSECRETORY))})")
    
    print(f"\nConnections (neuron-to-neuron only): {len(connections)}")
    print(f"Total synapse weight: {sum(connections.values()):.1f}")
    
    # Count by type
    inter_to_motor = sum(w for (s, t), w in connections.items() 
                         if s in INTERNEURONS and t in MOTOR_NEURONS)
    motor_to_inter = sum(w for (s, t), w in connections.items() 
                         if s in MOTOR_NEURONS and t in INTERNEURONS)
    print(f"\nInterneuron -> Motor weight: {inter_to_motor:.1f}")
    print(f"Motor -> Interneuron weight: {motor_to_inter:.1f}")
    
    print("\n" + "=" * 70)
    print("LEAN4 CODE")
    print("=" * 70 + "\n")
    print_lean_code(matrix, connections)
    
    print("\n" + "=" * 70)
    print("EDGE LIST")
    print("=" * 70)
    print_edge_list(connections)
    
    # Save adjacency matrix to CSV
    with open('pharynx_adjacency.csv', 'w') as f:
        f.write("," + ",".join(PHARYNGEAL_NEURONS) + "\n")
        for i, row in enumerate(matrix):
            f.write(PHARYNGEAL_NEURONS[i] + "," + ",".join([f"{v:.1f}" for v in row]) + "\n")
    print("\n\nAdjacency matrix saved to pharynx_adjacency.csv")

if __name__ == "__main__":
    main()
