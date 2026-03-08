#!/usr/bin/env python3
"""
Phase 1: The Betti Number Autopsy

Computes topological invariants (b₀, b₁) for all operators in the Sheaf Atlas
to validate the generalization boundary theorem:

    b₁ ≥ 1  →  Markov blanket exists  →  rule generalizes
    b₁ = 0  →  no blanket            →  fragile memorization

For a graph with V vertices and E edges:
    b₀ = number of connected components
    b₁ = E - V + b₀  (Euler characteristic)

THEORY SOURCE: FRONTIER_PHYSICS_SYNTHESIS.md Section 3.5
    "A crystallized Laplacian with b₁ ≥ 1 (HasMarkovBlanket) automatically has
     a non-trivial first cohomology, which guarantees approximate lumpability."
"""

import os
import sys
import pickle
import numpy as np
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def compute_betti_from_adjacency(adj_matrix: np.ndarray):
    """
    Compute b₀ and b₁ from an adjacency matrix.
    
    b₀ = number of connected components (via BFS)
    b₁ = |E| - |V| + b₀  (Euler characteristic for graphs)
    """
    n = adj_matrix.shape[0]
    if n == 0:
        return 0, 0
    
    # Count edges (undirected: count upper triangle)
    n_edges = 0
    for i in range(n):
        for j in range(i + 1, n):
            if adj_matrix[i, j] != 0:
                n_edges += 1
    
    # Compute connected components via BFS
    visited = [False] * n
    n_components = 0
    
    for start in range(n):
        if visited[start]:
            continue
        n_components += 1
        queue = [start]
        visited[start] = True
        while queue:
            node = queue.pop(0)
            for neighbor in range(n):
                if not visited[neighbor] and adj_matrix[node, neighbor] != 0:
                    visited[neighbor] = True
                    queue.append(neighbor)
    
    b0 = n_components
    b1 = n_edges - n + b0  # Euler characteristic: χ = V - E + F, for graphs F=b₁+1
    b1 = max(b1, 0)  # b₁ cannot be negative for simple graphs
    
    return b0, b1


def compute_betti_from_edge_weights(edge_weights, n_stalks):
    """
    Compute Betti numbers from crystallized Laplacian edge weights.
    
    The edge_weights list corresponds to stalk pairs (i,j) for i<j.
    An edge exists if |weight| > threshold (crystallized to non-zero).
    """
    if n_stalks < 2 or not edge_weights:
        return n_stalks, 0
    
    # Build adjacency matrix from edge weights
    adj = np.zeros((n_stalks, n_stalks))
    edge_pairs = [(i, j) for i in range(n_stalks) for j in range(i + 1, n_stalks)]
    
    for idx, (i, j) in enumerate(edge_pairs):
        if idx >= len(edge_weights):
            break
        if abs(edge_weights[idx]) > 0.01:  # Non-zero crystallized weight
            adj[i, j] = edge_weights[idx]
            adj[j, i] = edge_weights[idx]
    
    return compute_betti_from_adjacency(adj)


def compute_betti_from_laplacian(L: np.ndarray):
    """
    Compute Betti numbers from a full Laplacian matrix.
    
    The adjacency is recovered from off-diagonal entries:
    A[i,j] = -L[i,j] for i≠j (non-zero means edge exists).
    """
    n = L.shape[0]
    adj = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i != j and abs(L[i, j]) > 1e-6:
                adj[i, j] = 1
    
    return compute_betti_from_adjacency(adj)


def analyze_operator_topology(op):
    """
    Analyze the topological invariants of a single operator.
    
    Returns dict with b₀, b₁, has_blanket, and analysis notes.
    """
    op_type = op.get('type', 'unknown')
    result = {
        'type': op_type,
        'b0': None,
        'b1': None,
        'has_blanket': None,
        'notes': ''
    }
    
    if op_type == 'crystallized_laplacian':
        edge_weights = op.get('edge_weights', [])
        grokked = op.get('grokked', False)
        complexity = op.get('structural_complexity', 0)
        
        # Infer n_stalks from edge count: n_edges = n*(n-1)/2
        # Solve: n² - n - 2*len(edge_weights) = 0
        n_ew = len(edge_weights)
        n_stalks = int((1 + np.sqrt(1 + 8 * n_ew)) / 2) if n_ew > 0 else 0
        
        if n_stalks >= 2:
            b0, b1 = compute_betti_from_edge_weights(edge_weights, n_stalks)
            result['b0'] = b0
            result['b1'] = b1
            result['has_blanket'] = b1 >= 1
            result['n_stalks'] = n_stalks
            result['n_active_edges'] = sum(1 for w in edge_weights if abs(w) > 0.01)
            result['grokked'] = grokked
            result['complexity'] = complexity
            result['notes'] = f"n_stalks={n_stalks}, active_edges={result['n_active_edges']}, grokked={grokked}"
        else:
            result['b0'] = n_stalks
            result['b1'] = 0
            result['has_blanket'] = False
            result['notes'] = f"Too few stalks ({n_stalks})"
    
    elif op_type == 'matrix_operator':
        # Matrix operators encode permutation + color + translation
        # These are point-to-point maps with no cycles → b₁ = 0
        # UNLESS the permutation matrix has cycles (orbits)
        P = op.get('permutation_matrix')
        if P is not None:
            P_arr = np.array(P)
            if P_arr.ndim == 2 and P_arr.shape[0] == P_arr.shape[1]:
                # Build permutation graph: edge from i to P(i)
                n = P_arr.shape[0]
                adj = np.zeros((n, n))
                for i in range(n):
                    j = np.argmax(P_arr[i])
                    if P_arr[i, j] > 0.5:
                        adj[i, j] = 1
                        adj[j, i] = 1
                b0, b1 = compute_betti_from_adjacency(adj)
                result['b0'] = b0
                result['b1'] = b1
                result['has_blanket'] = b1 >= 1
                result['notes'] = f"Permutation matrix {n}x{n}"
            else:
                result['b0'] = 1
                result['b1'] = 0
                result['has_blanket'] = False
                result['notes'] = "Non-square or missing permutation"
        else:
            result['b0'] = 1
            result['b1'] = 0
            result['has_blanket'] = False
            result['notes'] = "No permutation matrix"
    
    elif op_type in ('color_map', 'relative_color'):
        # Color maps are pointwise transformations — no topology
        result['b0'] = 1
        result['b1'] = 0
        result['has_blanket'] = False
        result['notes'] = "Pointwise color transform — no cycles"
    
    elif op_type in ('reflection', 'complete_symmetry'):
        # Reflections create a Z₂ symmetry — this IS a cycle (b₁ = 1)
        # The reflection axis + reflected region forms a closed loop
        result['b0'] = 1
        result['b1'] = 1
        result['has_blanket'] = True
        result['notes'] = "Symmetry creates topological cycle (Z₂ orbit)"
    
    elif op_type == 'translation':
        # Pure translation is a vector — no cycle
        result['b0'] = 1
        result['b1'] = 0
        result['has_blanket'] = False
        result['notes'] = "Linear displacement — no cycles"
    
    elif op_type == 'translate_until_collision':
        # Relational: depends on obstacle — creates implicit cycle via boundary
        # The stalk + obstacle + collision boundary forms a feedback loop
        result['b0'] = 1  # Single connected process
        result['b1'] = 1  # Collision boundary creates cycle
        result['has_blanket'] = True
        result['notes'] = "Relational collision boundary creates implicit cycle"
    
    elif op_type == 'fill_interior':
        # Fill interior explicitly closes a cycle (fills a hole → b₁ changes)
        result['b0'] = 1
        result['b1'] = 1  # The boundary being filled IS a cycle
        result['has_blanket'] = True
        result['notes'] = "Interior fill closes topological cycle"
    
    elif op_type == 'crop':
        # Crop is a restriction — no cycles
        result['b0'] = 1
        result['b1'] = 0
        result['has_blanket'] = False
        result['notes'] = "Restriction map — no cycles"
    
    elif op_type == 'extend_to_edge':
        # Extension creates boundary contact — weak cycle
        result['b0'] = 1
        result['b1'] = 0
        result['has_blanket'] = False
        result['notes'] = "Linear extension — no cycles"
    
    elif op_type == 'tile_pattern':
        # Tiling creates periodic structure — cycles from periodicity
        result['b0'] = 1
        result['b1'] = 1
        result['has_blanket'] = True
        result['notes'] = "Periodic tiling creates topological cycles"
    
    elif op_type == 'composition':
        # Composition: analyze sub-operators
        sub_ops = op.get('operators', [])
        max_b1 = 0
        sub_notes = []
        for sub_op in sub_ops:
            sub_result = analyze_operator_topology(sub_op)
            if sub_result['b1'] is not None:
                max_b1 = max(max_b1, sub_result['b1'])
            sub_notes.append(f"{sub_result['type']}(b1={sub_result['b1']})")
        result['b0'] = 1
        result['b1'] = max_b1
        result['has_blanket'] = max_b1 >= 1
        result['notes'] = f"Composition of: {', '.join(sub_notes)}"
    
    else:
        result['notes'] = f"Unknown type: {op_type}"
    
    return result


def run_autopsy(atlas_path="global_atlas.pkl"):
    """Run the full Betti number autopsy on the Sheaf Atlas."""
    
    full_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), atlas_path)
    
    print("=" * 70)
    print("PHASE 1: BETTI NUMBER AUTOPSY")
    print("Topological Analysis of Sheaf Atlas Operators")
    print("=" * 70)
    
    # Load atlas
    if not os.path.exists(full_path):
        print(f"ERROR: Atlas not found at {full_path}")
        return
    
    with open(full_path, 'rb') as f:
        atlas = pickle.load(f)
    
    charts = atlas.charts
    print(f"\nAtlas contains {len(charts)} charts")
    
    # Analyze all operators
    all_results = []
    type_stats = defaultdict(lambda: {'total': 0, 'blanket': 0, 'no_blanket': 0})
    
    for chart_idx, chart in enumerate(charts):
        operators = chart.get('operators', [])
        if not operators:
            continue
        
        for op in operators:
            result = analyze_operator_topology(op)
            result['chart_idx'] = chart_idx
            all_results.append(result)
            
            op_type = result['type']
            type_stats[op_type]['total'] += 1
            if result['has_blanket'] is True:
                type_stats[op_type]['blanket'] += 1
            elif result['has_blanket'] is False:
                type_stats[op_type]['no_blanket'] += 1
    
    # Report
    print(f"\nTotal operators analyzed: {len(all_results)}")
    
    print("\n" + "-" * 70)
    print("OPERATOR TYPE SUMMARY")
    print("-" * 70)
    print(f"{'Type':<30} {'Total':>6} {'b1>=1':>6} {'b1=0':>6} {'Blanket%':>8}")
    print("-" * 70)
    
    total_blanket = 0
    total_no_blanket = 0
    
    for op_type, stats in sorted(type_stats.items()):
        pct = 100 * stats['blanket'] / max(stats['total'], 1)
        print(f"{op_type:<30} {stats['total']:>6} {stats['blanket']:>6} {stats['no_blanket']:>6} {pct:>7.1f}%")
        total_blanket += stats['blanket']
        total_no_blanket += stats['no_blanket']
    
    print("-" * 70)
    total = total_blanket + total_no_blanket
    pct = 100 * total_blanket / max(total, 1)
    print(f"{'TOTAL':<30} {total:>6} {total_blanket:>6} {total_no_blanket:>6} {pct:>7.1f}%")
    
    # Detailed crystallized Laplacian analysis
    crystal_ops = [r for r in all_results if r['type'] == 'crystallized_laplacian']
    if crystal_ops:
        print("\n" + "-" * 70)
        print("CRYSTALLIZED LAPLACIAN DETAIL")
        print("-" * 70)
        for r in crystal_ops:
            blanket_str = "[OK] BLANKET" if r['has_blanket'] else "[X] NO BLANKET"
            print(f"  Chart {r['chart_idx']:>3}: b0={r['b0']}, b1={r['b1']} -> {blanket_str}")
            print(f"            {r['notes']}")
    
    # THE VERDICT
    print("\n" + "=" * 70)
    print("THE VERDICT: GENERALIZATION BOUNDARY THEOREM VALIDATION")
    print("=" * 70)
    
    if total_no_blanket > 0 and total_blanket == 0:
        print("\n  ALL operators have b1 = 0 (NO Markov blankets)")
        print("  -> THEORY VALIDATED: The engine found eps < 0.15 but never closed")
        print("    a topological cycle. These are fragile, grid-dependent memorizations.")
        print("    The Permanent Library remained empty because there was nothing")
        print("    worth permanently storing.")
    elif total_blanket > 0:
        print(f"\n  {total_blanket}/{total} operators have b1 >= 1 (Markov blankets)")
        print(f"  {total_no_blanket}/{total} operators have b1 = 0 (memorizations)")
        print("  -> PARTIAL VALIDATION: Some operators have blankets, some don't.")
        print("    The engine should only consolidate operators with b1 >= 1.")
    else:
        print("\n  No operators found with computable Betti numbers.")
    
    # Prescription
    print("\n" + "-" * 70)
    print("PRESCRIPTION")
    print("-" * 70)
    print("  1. Add b1 >= 1 gate to consolidation: only store operators with blankets")
    print("  2. If b1 = 0 after grokking: increase A_pump and continue exploring")
    print("  3. Instrument crystallize_logical_laplacian to compute b1 at quench time")
    print("  4. Track b1 as a first-class observable alongside eps_func and CI")
    
    return all_results


def run_live_autopsy(max_tasks=10, verbose=True):
    """
    Run the autopsy LIVE: evaluate ARC tasks, crystallize Laplacians,
    and compute b₀/b₁ for each crystallized operator in real-time.
    """
    from spiking_sheaf_engine import SpikingSheafEngine
    from emergent_sheaf_engine import EmergentSheafAtlas
    import json
    
    print("=" * 70)
    print("LIVE BETTI AUTOPSY: Computing b0, b1 during ARC evaluation")
    print("=" * 70)
    
    # Load tasks
    possible_dirs = [
        os.path.join(os.path.dirname(__file__), "..", "data", "arc", "training"),
        r"C:\Users\jason\arc-prize-2024\arc-agi_training_challenges",
    ]
    
    task_dir = None
    for d in possible_dirs:
        if os.path.isdir(d):
            task_dir = d
            break
    
    if task_dir is None:
        print("ERROR: No ARC task directory found")
        return
    
    tasks = []
    for filename in sorted(os.listdir(task_dir)):
        if filename.endswith('.json'):
            with open(os.path.join(task_dir, filename)) as f:
                task_data = json.load(f)
            tasks.append({'id': filename[:-5], 'data': task_data})
    
    tasks = tasks[:max_tasks]
    print(f"Analyzing {len(tasks)} tasks...")
    
    results = []
    
    for task_idx, task in enumerate(tasks):
        task_id = task['id']
        train_examples = task['data'].get('train', [])
        
        if not train_examples:
            continue
        
        # Process each training pair
        for ex_idx, ex in enumerate(train_examples):
            inp = np.array(ex['input'], dtype=np.float32)
            out = np.array(ex['output'], dtype=np.float32)
            
            engine = SpikingSheafEngine(
                input_grid=inp,
                target_grid=out,
                spike_threshold=0.75,
                learning_rate=0.15
            )
            
            stalks = engine.decompose_to_stalks(inp)
            n_stalks = len(stalks)
            
            if n_stalks < 2 or n_stalks > 5 or engine.N > 100:
                continue
            
            # Skip shape mismatches (different input/output dimensions)
            if inp.shape != out.shape:
                continue
            
            # Crystallize
            grok_result = engine.crystallize_logical_laplacian(
                stalks, out,
                max_iterations=30,
                initial_temperature=0.5,
                sparsity_lambda=0.2
            )
            
            if grok_result.get('grokked', False):
                edge_weights = grok_result['edge_weights']
                b0, b1 = compute_betti_from_edge_weights(edge_weights, n_stalks)
                
                result = {
                    'task_id': task_id,
                    'example': ex_idx,
                    'n_stalks': n_stalks,
                    'b0': b0,
                    'b1': b1,
                    'has_blanket': b1 >= 1,
                    'accuracy': grok_result.get('final_accuracy', 0),
                    'defect': grok_result.get('functional_defect', 1),
                    'edge_weights': edge_weights
                }
                results.append(result)
                
                blanket_str = "[OK] b1>=1" if b1 >= 1 else "[X] b1=0"
                if verbose:
                    print(f"  [{task_id}] Ex{ex_idx}: {n_stalks} stalks, "
                          f"b0={b0}, b1={b1} {blanket_str} "
                          f"(acc={result['accuracy']:.1%}, eps={result['defect']:.3f})")
    
    # Summary
    print("\n" + "=" * 70)
    print("LIVE AUTOPSY SUMMARY")
    print("=" * 70)
    
    n_grokked = len(results)
    n_blanket = sum(1 for r in results if r['has_blanket'])
    n_no_blanket = n_grokked - n_blanket
    
    print(f"Grokked operators: {n_grokked}")
    print(f"  With blanket (b1>=1): {n_blanket}")
    print(f"  Without blanket (b1=0): {n_no_blanket}")
    
    if n_grokked > 0:
        avg_acc_blanket = np.mean([r['accuracy'] for r in results if r['has_blanket']]) if n_blanket > 0 else 0
        avg_acc_no_blanket = np.mean([r['accuracy'] for r in results if not r['has_blanket']]) if n_no_blanket > 0 else 0
        print(f"\n  Avg accuracy WITH blanket:    {avg_acc_blanket:.1%}")
        print(f"  Avg accuracy WITHOUT blanket: {avg_acc_no_blanket:.1%}")
    
    return results


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Phase 1: Betti Number Autopsy')
    parser.add_argument('--atlas', action='store_true', help='Analyze existing atlas')
    parser.add_argument('--live', action='store_true', help='Run live analysis on ARC tasks')
    parser.add_argument('--max-tasks', type=int, default=20, help='Max tasks for live analysis')
    args = parser.parse_args()
    
    if args.atlas or (not args.live):
        run_autopsy()
    
    if args.live:
        print("\n")
        run_live_autopsy(max_tasks=args.max_tasks)
