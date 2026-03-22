#!/usr/bin/env python3
"""
Phase 12: Multi-constraint manifold discovery on CERN dimuon data.
Discovers k=2 orthogonal quadratic constraints from raw 8D muon 4-vectors.
"""
import numpy as np
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from sgc_relational_engine import SGCRelationalEngine, load_cern_dimuon

csv_path = os.path.join(os.path.dirname(__file__), '..', 'data', 'MuRun2010B.csv')
csv_path = os.path.normpath(csv_path)

X_raw, M_oracle = load_cern_dimuon(csv_path)
global_scale = np.std(X_raw)
X = X_raw / global_scale

eta = np.diag([1, -1, -1, -1])

print("=" * 70)
print("PHASE 12: MULTI-CONSTRAINT MANIFOLD DISCOVERY (k=2)")
print("Raw 8D input, orthogonality constraint, no block prior")
print("=" * 70)

# Ground truth
for name, sl in [("Muon 1", slice(0,4)), ("Muon 2", slice(4,8))]:
    eta_norm = eta / np.linalg.norm(eta)
    q = np.einsum('ni,ij,nj->n', X[:, sl], eta_norm, X[:, sl])
    print(f"  {name} mass shell (eta/||eta||): var={np.var(q):.6e}")

# Run multi-constraint discovery
constraints, telemetry = SGCRelationalEngine.crystallize_manifold_multi(
    X, k=2, max_iterations=1000, lr=0.01
)

# Verification: compute per-block variance for each discovered constraint
print("\n" + "=" * 70)
print("VERIFICATION: Per-block mass shell variance")
print("=" * 70)

X_outer = np.einsum('ni,nj->nij', X, X)
eta_norm = eta / np.linalg.norm(eta)

for cidx, C in enumerate(constraints):
    print(f"\n  Constraint C_{cidx+1}:")
    q_full = np.einsum('ij,nij->n', C, X_outer)
    print(f"    Full 8D variance: {np.var(q_full):.6e}")
    
    for bname, sl in [("Muon 1 block", slice(0,4)), ("Muon 2 block", slice(4,8))]:
        block = C[sl, sl]
        bd = np.diag(block)
        q_block = np.einsum('ni,ij,nj->n', X[:, sl], block, X[:, sl])
        
        # Compare to exact eta on same block
        q_eta = np.einsum('ni,ij,nj->n', X[:, sl], eta_norm, X[:, sl])
        
        print(f"    {bname}:")
        print(f"      Diagonal: [{', '.join(f'{v:+.6f}' for v in bd)}]")
        if abs(bd[0]) > 0.001:
            ratios = bd[1:] / bd[0]
            err = np.max(np.abs(ratios - (-1.0)))
            print(f"      Ratios to E: [{', '.join(f'{r:+.4f}' for r in ratios)}] "
                  f"(Minkowski error: {err:.4f})")
        print(f"      Block variance: {np.var(q_block):.6e}")
        print(f"      Exact eta var:  {np.var(q_eta):.6e}")
        if np.var(q_eta) > 0:
            print(f"      Ratio to exact: {np.var(q_block)/np.var(q_eta):.1f}x")

# Physical units check
print(f"\n  Physical units (GeV^2):")
for cidx, C in enumerate(constraints):
    q_phys = np.einsum('ij,nij->n', C, X_outer) * global_scale**2
    print(f"    C_{cidx+1}: mean={np.mean(q_phys):.6f} GeV^2, "
          f"std={np.std(q_phys):.6f} GeV^2, "
          f"sqrt(|mean|)={np.sqrt(abs(np.mean(q_phys))):.4f} GeV "
          f"(m_mu=0.106)")
