#!/usr/bin/env python3
"""
SGC Block Tensor: Full 2x2 Constitutive Measurement

Measure the RESTRICTED K-step block norms:
  g_par->par = ||Pi M^K Pi||
  g_par->perp = ||(I-Pi) M^K Pi||
  g_perp->par = ||Pi M^K (I-Pi)||
  g_perp->perp = ||(I-Pi) M^K (I-Pi)||

This is the full 2x2 constitutive tensor needed for block-aware control.

From this we can derive:
1. Block row-sum bound for contractivity
2. Whether Schur-complement-aware damping is needed
3. The minimal robust scalar damping

Author: SGC Project
"""

import argparse
import numpy as np
import torch
import torch.nn.functional as F
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.iterative_spectral_refinement import (
    ISRSolver, SudokuDataset
)


def jvp_finite_diff(model, z, x_enc, v, eps=1e-4):
    """Compute Jv via finite differences."""
    z_flat = z.view(-1)
    v_flat = v.view(-1)
    
    def F_func(z_f):
        B, N, D = z.shape
        z_shaped = z_f.view(B, N, D)
        z_combined = z_shaped + x_enc
        for block in model.blocks:
            z_combined = block(z_combined)
        return z_combined.view(-1)
    
    with torch.no_grad():
        F_plus = F_func(z_flat + eps * v_flat)
        F_minus = F_func(z_flat - eps * v_flat)
    
    Jv_flat = (F_plus - F_minus) / (2 * eps)
    return Jv_flat.view(z.shape)


def measure_block_tensor_K_step(model, z, x_enc, K, alpha, n_probes=30):
    """Measure the full 2x2 block tensor at horizon K.
    
    Returns the RESTRICTED block norms:
      g[i->j] = ||P_j M^K P_i|| where P_par = Pi, P_perp = I-Pi
    """
    B, N, D = z.shape
    
    norms = {
        'par_to_par': [],   # ||Pi M^K Pi||
        'par_to_perp': [],  # ||(I-Pi) M^K Pi||
        'perp_to_par': [],  # ||Pi M^K (I-Pi)||
        'perp_to_perp': [], # ||(I-Pi) M^K (I-Pi)||
    }
    
    for _ in range(n_probes):
        # Probe in HORIZONTAL subspace
        v_par = torch.randn_like(z)
        v_par = model.Pi(v_par)
        if v_par.norm() > 1e-8:
            v_par = v_par / v_par.norm()
            
            # Apply M_alpha K times
            v_k = v_par.clone()
            for _ in range(K):
                Jv = jvp_finite_diff(model, z, x_enc, v_k)
                v_k = (1 - alpha) * v_k + alpha * Jv
            
            # Project result
            v_k_par = model.Pi(v_k)
            v_k_perp = v_k - v_k_par
            
            norms['par_to_par'].append(v_k_par.norm().item())
            norms['par_to_perp'].append(v_k_perp.norm().item())
        
        # Probe in VERTICAL subspace
        v_perp = torch.randn_like(z)
        v_perp = v_perp - model.Pi(v_perp)
        if v_perp.norm() > 1e-8:
            v_perp = v_perp / v_perp.norm()
            
            # Apply M_alpha K times
            v_k = v_perp.clone()
            for _ in range(K):
                Jv = jvp_finite_diff(model, z, x_enc, v_k)
                v_k = (1 - alpha) * v_k + alpha * Jv
            
            # Project result
            v_k_par = model.Pi(v_k)
            v_k_perp = v_k - v_k_par
            
            norms['perp_to_par'].append(v_k_par.norm().item())
            norms['perp_to_perp'].append(v_k_perp.norm().item())
    
    # Return max over probes (operator norm estimate)
    return {k: np.max(v) if v else 0.0 for k, v in norms.items()}


def block_row_sum_bound(tensor):
    """Compute block row-sum bound for contractivity.
    
    A sufficient condition for ||M|| <= 1 is that each block row sums to <= 1.
    This is a standard move in operator norm bounding.
    """
    row_par = tensor['par_to_par'] + tensor['perp_to_par']
    row_perp = tensor['par_to_perp'] + tensor['perp_to_perp']
    return max(row_par, row_perp)


def main():
    parser = argparse.ArgumentParser(description="SGC Block Tensor")
    parser.add_argument('--num_puzzles', type=int, default=200)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--train_epochs', type=int, default=50)
    parser.add_argument('--n_probes', type=int, default=30)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Block Tensor] Device: {device}")
    print("="*70)
    print("FULL 2x2 CONSTITUTIVE TENSOR MEASUREMENT")
    print("="*70)
    
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Train model
    print(f"\n[1/3] Training model...")
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
    
    # Get test state
    test_puzzle = puzzles[0:1].to(device)
    with torch.no_grad():
        x_enc = model.encode_puzzle(test_puzzle)
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
        for _ in range(30):
            _, z = model.forward_step(z, x_enc)
    
    # Measure block tensor at K=1 (one-step Jacobian)
    print(f"\n[2/3] Measuring one-step (K=1) block tensor...")
    
    print(f"\n  ONE-STEP RESTRICTED BLOCK NORMS (J, not M^K):")
    print(f"  | alpha | par->par | par->perp | perp->par | perp->perp | row_max |")
    print(f"  |-------|----------|-----------|-----------|------------|---------|")
    
    for alpha in [1.0, 0.5, 0.2, 0.1]:
        tensor = measure_block_tensor_K_step(model, z, x_enc, K=1, alpha=alpha, n_probes=args.n_probes)
        row_max = block_row_sum_bound(tensor)
        print(f"  | {alpha:5.2f} | {tensor['par_to_par']:8.3f} | {tensor['par_to_perp']:9.3f} | {tensor['perp_to_par']:9.3f} | {tensor['perp_to_perp']:10.3f} | {row_max:7.3f} |")
    
    # Measure block tensor at K=30 and K=100
    print(f"\n[3/3] Measuring K-step block tensors...")
    
    for K in [30, 100]:
        print(f"\n  K={K} RESTRICTED BLOCK NORMS:")
        print(f"  | alpha | par->par | par->perp | perp->par | perp->perp | row_max |")
        print(f"  |-------|----------|-----------|-----------|------------|---------|")
        
        for alpha in [1.0, 0.5, 0.2, 0.1, 0.05]:
            tensor = measure_block_tensor_K_step(model, z, x_enc, K=K, alpha=alpha, n_probes=args.n_probes)
            row_max = block_row_sum_bound(tensor)
            marker = " <--" if row_max <= 1.0 else ""
            print(f"  | {alpha:5.2f} | {tensor['par_to_par']:8.3f} | {tensor['par_to_perp']:9.3f} | {tensor['perp_to_par']:9.3f} | {tensor['perp_to_perp']:10.3f} | {row_max:7.3f} |{marker}")
    
    # Summary
    print("\n" + "="*70)
    print("CONSTITUTIVE TENSOR ANALYSIS")
    print("="*70)
    
    # Get the key tensor at alpha=0.1, K=100
    tensor_01 = measure_block_tensor_K_step(model, z, x_enc, K=100, alpha=0.1, n_probes=args.n_probes)
    tensor_10 = measure_block_tensor_K_step(model, z, x_enc, K=100, alpha=1.0, n_probes=args.n_probes)
    
    print(f"""
  At K=100, alpha=1.0 (undamped):
    | {tensor_10['par_to_par']:.3f}  {tensor_10['perp_to_par']:.3f} |
    | {tensor_10['par_to_perp']:.3f}  {tensor_10['perp_to_perp']:.3f} |
    Block row-sum: {block_row_sum_bound(tensor_10):.3f}

  At K=100, alpha=0.1 (damped):
    | {tensor_01['par_to_par']:.3f}  {tensor_01['perp_to_par']:.3f} |
    | {tensor_01['par_to_perp']:.3f}  {tensor_01['perp_to_perp']:.3f} |
    Block row-sum: {block_row_sum_bound(tensor_01):.3f}

  KEY OBSERVATIONS:
  1. par->perp (horizontal pumping vertical): {tensor_10['par_to_perp']:.3f} at alpha=1
     This is WHY increasing alpha_par breaks things!
  
  2. perp->perp (vertical self-amplification): {tensor_10['perp_to_perp']:.3f} at alpha=1
     This is the main instability source.
  
  3. With alpha=0.1:
     - par->perp drops to {tensor_01['par_to_perp']:.3f}
     - perp->perp drops to {tensor_01['perp_to_perp']:.3f}
     - Block row-sum: {block_row_sum_bound(tensor_01):.3f}

  CONSTITUTIVE LAW (block form):
    Choose alpha such that block row-sum <= G* = 1 + delta
    
    At alpha=0.1: row_sum = {block_row_sum_bound(tensor_01):.3f}
    
  This is the full 2x2 tensor that a Schur-complement-aware controller
  would need to handle. Scalar KM is robust because it suppresses ALL blocks.
""")


if __name__ == '__main__':
    main()
