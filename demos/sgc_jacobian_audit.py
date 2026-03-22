#!/usr/bin/env python3
"""
SGC Jacobian Audit: Rigorous Verification

This script addresses the critique that "L=1.0" may be an artifact.

Verification steps:
1. Sanity check: Compare JVP to finite differences
2. Distribution: ||(J-I)v||/||v|| across many probes/puzzles/timesteps
3. Block norms: All Pi-split components including cross terms
4. Statistics: Mean, std, min, max - not just point estimates

The honest question: Is ||J-I|| a reproducible constitutive constant,
or is it an artifact of the measurement procedure?

Author: SGC Project
"""

import argparse
import numpy as np
import torch
import torch.nn.functional as F
from torch.autograd.functional import jvp
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.iterative_spectral_refinement import (
    ISRSolver, SudokuDataset
)


def jvp_finite_diff(model, z, x_enc, v, eps=1e-4):
    """Compute Jv via finite differences."""
    B, N, D = z.shape
    with torch.no_grad():
        z_plus = z + eps * v
        z_minus = z - eps * v
        _, F_plus = model.forward_step(z_plus, x_enc)
        _, F_minus = model.forward_step(z_minus, x_enc)
        Jv_fd = (F_plus - F_minus) / (2 * eps)
    return Jv_fd


def jvp_autograd(model, z, x_enc, v):
    """Compute Jv via autograd JVP."""
    B, N, D = z.shape
    
    def F_func(z_input):
        z_reshaped = z_input.view(B, N, D)
        _, z_next = model.forward_step(z_reshaped, x_enc)
        return z_next.view(-1)
    
    z_flat = z.view(-1).requires_grad_(True)
    v_flat = v.view(-1)
    
    try:
        _, Jv = jvp(F_func, (z_flat,), (v_flat,))
        return Jv.view(B, N, D)
    except Exception as e:
        print(f"  [WARNING] Autograd JVP failed: {e}")
        return None


def sanity_check_jvp(model, z, x_enc, n_probes=10):
    """Compare JVP methods to verify correctness."""
    print("\n  SANITY CHECK: JVP vs Finite Differences")
    
    errors = []
    for i in range(n_probes):
        v = torch.randn_like(z)
        v = v / v.norm()  # Normalize
        
        Jv_fd = jvp_finite_diff(model, z, x_enc, v)
        Jv_ag = jvp_autograd(model, z, x_enc, v)
        
        if Jv_ag is not None:
            rel_error = (Jv_fd - Jv_ag).norm() / (Jv_fd.norm() + 1e-8)
            errors.append(rel_error.item())
    
    if errors:
        mean_err = np.mean(errors)
        max_err = np.max(errors)
        print(f"    Relative error (FD vs autograd): mean={mean_err:.4f}, max={max_err:.4f}")
        if max_err > 0.1:
            print(f"    [WARNING] Large discrepancy - JVP may be unreliable!")
            return False
        else:
            print(f"    [OK] JVP methods agree")
            return True
    else:
        print(f"    [WARNING] Autograd JVP failed - using finite differences only")
        return False


def measure_gain_distribution(model, z, x_enc, n_probes=50):
    """Measure distribution of ||(J-I)v||/||v|| across many random probes.
    
    This is the key diagnostic: if L=1.0 is real, this ratio should
    concentrate near 1.0 across many random directions.
    """
    gains = []
    
    for _ in range(n_probes):
        v = torch.randn_like(z)
        v_norm = v.norm()
        
        # Compute (J-I)v = Jv - v
        Jv = jvp_finite_diff(model, z, x_enc, v)
        JmI_v = Jv - v
        
        # Gain = ||(J-I)v|| / ||v||
        gain = JmI_v.norm() / (v_norm + 1e-8)
        gains.append(gain.item())
    
    return np.array(gains)


def measure_block_norms(model, z, x_enc, n_probes=30):
    """Measure all Pi-split block norms including cross terms.
    
    The full decomposition:
    - ||Pi(J-I)Pi||: horizontal self-coupling
    - ||(I-Pi)(J-I)(I-Pi)||: vertical self-coupling  
    - ||Pi(J-I)(I-Pi)||: vertical-to-horizontal leakage
    - ||(I-Pi)(J-I)Pi||: horizontal-to-vertical leakage
    
    The cross terms are the "leakage channels" in discrete time.
    """
    norms = {
        'h_to_h': [],  # Pi(J-I)Pi
        'v_to_v': [],  # (I-Pi)(J-I)(I-Pi)
        'v_to_h': [],  # Pi(J-I)(I-Pi)
        'h_to_v': [],  # (I-Pi)(J-I)Pi
        'total': [],   # J-I
    }
    
    for _ in range(n_probes):
        # Random probe in HORIZONTAL subspace
        v_h = torch.randn_like(z)
        v_h = model.Pi(v_h)
        if v_h.norm() > 1e-8:
            v_h = v_h / v_h.norm()
            
            Jv = jvp_finite_diff(model, z, x_enc, v_h)
            JmI_v = Jv - v_h
            
            # Project result
            JmI_v_h = model.Pi(JmI_v)
            JmI_v_v = JmI_v - JmI_v_h
            
            norms['h_to_h'].append(JmI_v_h.norm().item())
            norms['h_to_v'].append(JmI_v_v.norm().item())
        
        # Random probe in VERTICAL subspace
        v_v = torch.randn_like(z)
        v_v = v_v - model.Pi(v_v)
        if v_v.norm() > 1e-8:
            v_v = v_v / v_v.norm()
            
            Jv = jvp_finite_diff(model, z, x_enc, v_v)
            JmI_v = Jv - v_v
            
            JmI_v_h = model.Pi(JmI_v)
            JmI_v_v = JmI_v - JmI_v_h
            
            norms['v_to_h'].append(JmI_v_h.norm().item())
            norms['v_to_v'].append(JmI_v_v.norm().item())
        
        # Random probe in FULL space (for total norm)
        v = torch.randn_like(z)
        v = v / v.norm()
        Jv = jvp_finite_diff(model, z, x_enc, v)
        JmI_v = Jv - v
        norms['total'].append(JmI_v.norm().item())
    
    return {k: np.array(v) for k, v in norms.items()}


def main():
    parser = argparse.ArgumentParser(description="SGC Jacobian Audit")
    parser.add_argument('--num_puzzles', type=int, default=300)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--train_epochs', type=int, default=50)
    parser.add_argument('--n_puzzles_sample', type=int, default=20)
    parser.add_argument('--n_probes', type=int, default=50)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Jacobian Audit] Device: {device}")
    print("="*70)
    print("RIGOROUS VERIFICATION OF ||J-I|| MEASUREMENT")
    print("="*70)
    
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate and train
    print(f"\n[1/5] Training model...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    model = ISRSolver(args.hidden_dim, args.num_blocks).to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)
    batch_size = 64
    
    for epoch in range(args.train_epochs):
        model.train()
        total_loss = 0
        n_batches = 0
        indices = torch.randperm(len(puzzles))
        
        for i in range(0, len(puzzles), batch_size):
            batch_idx = indices[i:i+batch_size]
            p_batch = puzzles[batch_idx].to(device)
            s_batch = solutions[batch_idx].to(device)
            
            result = model(p_batch, T=30)
            loss = model.compute_loss(result['y_final'], s_batch, p_batch)
            
            optimizer.zero_grad()
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            total_loss += loss.item()
            n_batches += 1
        
        if (epoch + 1) % 10 == 0:
            model.eval()
            with torch.no_grad():
                out = model(puzzles[:100].to(device), T=30)
                acc = model.compute_accuracy(out['y_final'], solutions[:100].to(device), puzzles[:100].to(device))
            print(f"  Epoch {epoch+1}: loss={total_loss/n_batches:.4f}, solved={acc['solved_acc']*100:.1f}%")
    
    model.eval()
    
    # Sanity check JVP
    print(f"\n[2/5] Sanity checking JVP implementation...")
    test_puzzle = puzzles[:1].to(device)
    with torch.no_grad():
        x_enc = model.encode_puzzle(test_puzzle)
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
        for _ in range(30):
            _, z = model.forward_step(z, x_enc)
    
    jvp_ok = sanity_check_jvp(model, z, x_enc)
    
    # Distribution across puzzles and timesteps
    print(f"\n[3/5] Measuring ||J-I|| distribution across puzzles/timesteps...")
    
    all_gains = {'t=0': [], 't=10': [], 't=30': [], 't=50': [], 't=100': []}
    timesteps = [0, 10, 30, 50, 100]
    
    for p_idx in range(min(args.n_puzzles_sample, len(puzzles))):
        puzzle = puzzles[p_idx:p_idx+1].to(device)
        
        with torch.no_grad():
            x_enc = model.encode_puzzle(puzzle)
            z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
        
        for t in range(max(timesteps) + 1):
            if t in timesteps:
                # Measure at this timestep
                gains = measure_gain_distribution(model, z, x_enc, n_probes=args.n_probes)
                all_gains[f't={t}'].extend(gains.tolist())
            
            # Advance
            with torch.no_grad():
                _, z = model.forward_step(z, x_enc)
    
    print(f"\n  GAIN DISTRIBUTION: ||(J-I)v||/||v||")
    print(f"  (across {args.n_puzzles_sample} puzzles x {args.n_probes} probes)")
    print(f"  " + "-"*60)
    print(f"  | Timestep | Mean   | Std    | Min    | Max    |")
    print(f"  |----------|--------|--------|--------|--------|")
    for t in timesteps:
        g = np.array(all_gains[f't={t}'])
        print(f"  | t={t:3d}    | {g.mean():.4f} | {g.std():.4f} | {g.min():.4f} | {g.max():.4f} |")
    
    # Check if L=1.0 is real
    all_g = np.concatenate([np.array(v) for v in all_gains.values()])
    print(f"\n  OVERALL: mean={all_g.mean():.4f}, std={all_g.std():.4f}")
    print(f"           min={all_g.min():.4f}, max={all_g.max():.4f}")
    
    # Block norms including cross terms
    print(f"\n[4/5] Measuring Pi-split block norms (including cross terms)...")
    
    # Sample at t=30
    puzzle = puzzles[0:1].to(device)
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzle)
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
        for _ in range(30):
            _, z = model.forward_step(z, x_enc)
    
    block_norms = measure_block_norms(model, z, x_enc, n_probes=args.n_probes)
    
    print(f"\n  BLOCK NORMS at t=30:")
    print(f"  " + "-"*60)
    print(f"  | Block              | Mean   | Std    | Max    |")
    print(f"  |--------------------|--------|--------|--------|")
    for name, values in block_norms.items():
        if len(values) > 0:
            print(f"  | {name:18s} | {values.mean():.4f} | {values.std():.4f} | {values.max():.4f} |")
    
    # Cross-term analysis
    print(f"\n  LEAKAGE CHANNELS (cross terms):")
    h_to_v = block_norms['h_to_v']
    v_to_h = block_norms['v_to_h']
    print(f"    Horizontal -> Vertical: mean={h_to_v.mean():.4f}")
    print(f"    Vertical -> Horizontal: mean={v_to_h.mean():.4f}")
    
    # Final assessment
    print("\n" + "="*70)
    print("[5/5] ASSESSMENT")
    print("="*70)
    
    # Is L=1.0 an artifact?
    if all_g.std() < 0.1 and 0.9 < all_g.mean() < 1.1:
        print(f"\n  [SUSPICIOUS] ||J-I|| concentrates near 1.0 with low variance")
        print(f"  This could be due to:")
        print(f"    - LayerNorm/tanh forcing gain near 1 in Euclidean norm")
        print(f"    - Normalization leakage in measurement")
        print(f"    - A real constitutive property of the architecture")
    elif all_g.std() > 0.3:
        print(f"\n  [VARIABLE] ||J-I|| has high variance across states")
        print(f"  Need state-dependent alpha, not global constant")
    else:
        print(f"\n  [PLAUSIBLE] ||J-I|| shows moderate concentration")
        print(f"  Could be a measurable control parameter")
    
    # Honest statement
    print("\n" + "="*70)
    print("HONEST STATEMENT")
    print("="*70)
    
    print(f"""
  What we can claim:
  - ||J-I|| is a MEASURABLE quantity (mean={all_g.mean():.2f}, std={all_g.std():.2f})
  - alpha = q/||J-I|| is an ENGINEERING CONTROL LAW (cap local gain)
  - With q=0.1, alpha ~= 0.1/{all_g.mean():.2f} = {0.1/all_g.mean():.3f}
  
  What we CANNOT yet claim:
  - q=0.1 is derived from first principles
  - This is a Jacobson-style "equation of state"
  - ||J-I|| is a true constitutive constant (vs architecture artifact)
  
  The skeptic's view: "You moved the hyperparameter from alpha to q."
  
  To make this first-principles, we would need:
  - Derive q from entropy production bound
  - Or: tie q to NCD spectral gap gamma
  - Or: prove convergence rate guarantee that determines q
""")
    
    # Return key measurements for the collaborator
    print("\n" + "="*70)
    print("RAW DATA FOR COLLABORATOR")
    print("="*70)
    print(f"""
  Measurement method: Finite differences (eps=1e-4)
  JVP sanity check: {'PASSED' if jvp_ok else 'FAILED/SKIPPED'}
  
  Samples:
    - {args.n_puzzles_sample} puzzles
    - {args.n_probes} random probes per (puzzle, timestep)
    - Timesteps: {timesteps}
  
  Results:
    ||J-I|| mean: {all_g.mean():.6f}
    ||J-I|| std:  {all_g.std():.6f}
    ||J-I|| min:  {all_g.min():.6f}
    ||J-I|| max:  {all_g.max():.6f}
    
  Block norms (t=30):
    ||Pi(J-I)Pi||:         mean={block_norms['h_to_h'].mean():.4f}
    ||(I-Pi)(J-I)(I-Pi)||: mean={block_norms['v_to_v'].mean():.4f}
    ||Pi(J-I)(I-Pi)||:     mean={block_norms['v_to_h'].mean():.4f}
    ||(I-Pi)(J-I)Pi||:     mean={block_norms['h_to_v'].mean():.4f}
""")


if __name__ == '__main__':
    main()
