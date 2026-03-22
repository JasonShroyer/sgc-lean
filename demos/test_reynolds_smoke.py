#!/usr/bin/env python3
"""Smoke test for the SGC Reynolds Number Engine."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np
from sgc_reynolds_engine import (
    ReynoldsCrystallizer, decompose_stalks, EdgeState,
    build_edge_pairs, build_adjacency, build_laplacian,
    find_bridges, compute_b1, compute_forman_ricci,
    compute_defect_gradient_per_edge, compute_re_sgc,
    compute_lambda_pump_eigenspace, map_pump_eigen_to_edges,
    classify_zones, localized_fermi_quench, fermi,
    grid_to_sheaf, ThermoZone
)

print("=" * 60)
print("SGC REYNOLDS ENGINE — SMOKE TEST")
print("=" * 60)

# --- Test 1: Topology primitives ---
print("\n[1] Topology primitives...")
n_stalks = 4
edge_pairs = build_edge_pairs(n_stalks)
assert len(edge_pairs) == 6, f"Expected 6 edges, got {len(edge_pairs)}"

# edge_pairs for 4 stalks: (0,1)=0, (0,2)=1, (0,3)=2, (1,2)=3, (1,3)=4, (2,3)=5
# Triangle graph: edges (0,1), (0,2), (1,2) active
weights = np.array([0.5, 0.5, 0.0, 0.5, 0.0, 0.0], dtype=np.float32)
b1 = compute_b1(weights, edge_pairs, n_stalks)
print(f"  Triangle b1 = {b1} (expect 1)")
assert b1 == 1

bridges = find_bridges(weights, edge_pairs, n_stalks)
print(f"  Bridges: {bridges} (expect all False for triangle edges)")
assert not any(bridges[:3]), "Triangle edges should not be bridges"

# Add a bridge edge (0,3) at index 2
weights[2] = 0.5  # edge (0,3)
bridges2 = find_bridges(weights, edge_pairs, n_stalks)
print(f'  With bridge (0,3): bridges={bridges2}')
assert bridges2[2], "Edge (0,3) should be a bridge"
print("  PASSED")

# --- Test 2: Forman-Ricci curvature ---
print("\n[2] Forman-Ricci curvature...")
curvature = compute_forman_ricci(weights, edge_pairs, n_stalks)
print(f"  Curvature: {curvature}")
# Triangle edges: F = #triangles - 1 = 0 (one triangle -> F=0, protected)
assert curvature[0] >= 0, "Edge (0,1) in triangle should have F >= 0"
# Bridge edge (0,3) at index 2: no triangles -> F = -1
assert curvature[2] < 0, "Bridge (0,3) should have F < 0"
print("  PASSED")

# --- Test 3: EdgeState initialization ---
print("\n[3] EdgeState initialization...")
es = EdgeState.initialize(6)
assert es.n_edges == 6
assert len(es.weights) == 6
assert all(es.zone == ThermoZone.FRONTIER), "All edges start FRONTIER"
assert not any(es.crystallized), "No edges start crystallized"
print("  PASSED")

# --- Test 4: Re_SGC computation ---
print("\n[4] Re_SGC computation...")
kappa = np.array([0.3, 0.3, 0.3, 0.0, 0.3, 0.3], dtype=np.float32)
lp = np.array([1.0, 1.0, 0.0, 0.0, 1.0, 1.0], dtype=np.float32)
dg = np.array([0.1, 0.5, 0.1, 0.1, 0.01, 1.0], dtype=np.float32)
re = compute_re_sgc(kappa, 1.0, lp, dg)
print(f"  Re_SGC: {re}")
# Edge with kappa=0 or lambda_pump=0 should have Re=0
assert re[2] == 0.0, "Zero pump -> Re=0"
assert re[3] == 0.0, "Zero kappa -> Re=0"
# Edge with low defect grad should have high Re
assert re[4] > re[1], "Low defect grad -> higher Re"
print("  PASSED")

# --- Test 5: Zone classification ---
print("\n[5] Zone classification...")
re_crit = 1.0
crystallized = np.array([False, False, False, True, False, False])
zones = classify_zones(re, re_crit, crystallized)
print(f"  Zones: {zones}")
assert zones[3] == ThermoZone.CRYSTALLIZED, "Crystallized flag overrides"
assert zones[2] == ThermoZone.CRYSTALLIZED, "Re=0 -> crystallized zone"
print("  PASSED")

# --- Test 6: Lambda_pump eigenspace ---
print("\n[6] Lambda_pump eigenspace (HG nozzle)...")
eigenvalues = np.array([0.0, 0.5, 1.5, 3.0], dtype=np.float32)
lpe = compute_lambda_pump_eigenspace(eigenvalues)
print(f"  Lambda_pump_eigen: {lpe}")
assert lpe[0] == 0.0, "Zero eigenvalue -> zero pump"
assert lpe[1] > 0, "Non-zero eigenvalue -> positive pump"
print("  PASSED")

# --- Test 7: Localized Fermi quench ---
print("\n[7] Localized Fermi quench...")
es2 = EdgeState.initialize(4)
es2.weights = np.array([0.8, 0.3, -0.5, 0.1], dtype=np.float32)
es2.re_sgc = np.array([0.1, 5.0, 0.2, 10.0], dtype=np.float32)
es2, sigma_q, n_q = localized_fermi_quench(es2, re_crit=1.0, quench_sharpness=0.3)
print(f"  Sigma_quench: {sigma_q}")
print(f"  Newly crystallized: {n_q}")
# Low-Re edges should get high quench signal
assert sigma_q[0] > sigma_q[1], "Low Re -> higher quench signal"
assert sigma_q[3] < 0.1, "High Re -> low quench signal"
print("  PASSED")

# --- Test 8: Full engine on synthetic task ---
print("\n[8] Full engine — synthetic color recoloring task...")
inp = np.array([
    [0, 0, 0, 1, 0],
    [0, 1, 0, 0, 0],
    [0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0],
], dtype=np.float32)
out = np.array([
    [0, 0, 0, 2, 0],
    [0, 2, 0, 0, 0],
    [0, 0, 0, 0, 2],
    [2, 0, 0, 0, 0],
    [0, 0, 2, 0, 0],
], dtype=np.float32)

stalks = decompose_stalks(inp)
print(f"  Stalks found: {len(stalks)}")

engine = ReynoldsCrystallizer(n_colors=10, eta=0.01, initial_temp=1.0, re_crit=1.0)
result = engine.crystallize(inp, out, stalks, max_iterations=30)

print(f"\n  Results:")
print(f"    Grokked:    {result['grokked']}")
print(f"    b1:         {result['b1']}")
print(f"    Accuracy:   {result['final_accuracy']:.3f}")
print(f"    Defect:     {result['functional_defect']:.4f}")
print(f"    Zones:      {result['zones_final']}")
print(f"    Re_SGC:     {result['re_sgc_final']}")
print(f"    Quench evts:{result['n_quench_events']}")
print(f"    Iterations: {result['iterations']}")

# Verify telemetry recorded
telem = result['telemetry']
assert len(telem.b1) > 0, "Telemetry should have data"
assert len(telem.n_crystallized) > 0, "Zone tracking should have data"
assert len(telem.re_mean) > 0, "Re statistics should have data"
print("  PASSED")

print("\n" + "=" * 60)
print("ALL SMOKE TESTS PASSED")
print("=" * 60)
