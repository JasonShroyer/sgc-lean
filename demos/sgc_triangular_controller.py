#!/usr/bin/env python3
"""
SGC Triangular Controller: Minimal Schur-Complement Intervention

The key insight from block tensor analysis:
- par->perp = 2.235 at alpha=1.0 (the "pump" channel)
- Scalar KM cannot achieve block-inf contractivity (row_sum >= 1.418)

A triangular controller adds ONE off-diagonal term to kill the pump:

  Scalar KM:
    dz_par  = alpha * u_par
    dz_perp = alpha * u_perp

  Triangular:
    dz_par  = alpha * u_par
    dz_perp = alpha * u_perp - beta * u_par
    
The coefficient beta compensates for the par->perp gain.

Author: SGC Project
Date: January 30, 2026
"""

import torch
import torch.nn as nn
import numpy as np
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.iterative_spectral_refinement import ISRSolver, SudokuDataset


def triangular_forward_step(model, z, x_enc, alpha, beta):
    """Apply one step of triangular damped iteration."""
    _, z_next_raw = model.forward_step(z, x_enc)
    u = z_next_raw - z
    
    u_par = model.Pi(u)
    u_perp = u - u_par
    
    dz_par = alpha * u_par
    dz_perp = alpha * u_perp - beta * u_par
    
    z_new = z + dz_par + dz_perp
    return z_new


def triangular_inference(model, puzzle, x_enc, T, alpha, beta):
    """Run T steps of triangular-damped inference."""
    z = x_enc.clone()
    for _ in range(T):
        z = triangular_forward_step(model, z, x_enc, alpha, beta)
    y = model.to_logits(z + x_enc)
    return y, z


def measure_block_tensor(model, z, x_enc, K, alpha, beta, n_probes=30):
    """Measure the 2x2 block tensor under triangular control."""
    norms = {'par_to_par': [], 'par_to_perp': [], 'perp_to_par': [], 'perp_to_perp': []}
    eps = 1e-4
    
    for _ in range(n_probes):
        v = torch.randn_like(z)
        v_par = model.Pi(v)
        v_par = v_par / (v_par.norm() + 1e-8)
        
        v_k = v_par.clone()
        for _ in range(K):
            z_plus = z + eps * v_k
            z_minus = z - eps * v_k
            Fz_plus = triangular_forward_step(model, z_plus, x_enc, alpha, beta)
            Fz_minus = triangular_forward_step(model, z_minus, x_enc, alpha, beta)
            Mv = (Fz_plus - Fz_minus) / (2 * eps)
            v_k = Mv / (Mv.norm() + 1e-8)
        
        v_k_par = model.Pi(v_k)
        v_k_perp = v_k - v_k_par
        norms['par_to_par'].append(v_k_par.norm().item())
        norms['par_to_perp'].append(v_k_perp.norm().item())
        
        v_perp = torch.randn_like(z) 
        v_perp = v_perp - model.Pi(v_perp)
        v_perp = v_perp / (v_perp.norm() + 1e-8)
        
        v_k = v_perp.clone()
        for _ in range(K):
            z_plus = z + eps * v_k
            z_minus = z - eps * v_k
            Fz_plus = triangular_forward_step(model, z_plus, x_enc, alpha, beta)
            Fz_minus = triangular_forward_step(model, z_minus, x_enc, alpha, beta)
            Mv = (Fz_plus - Fz_minus) / (2 * eps)
            v_k = Mv / (Mv.norm() + 1e-8)
        
        v_k_par = model.Pi(v_k)
        v_k_perp = v_k - v_k_par
        norms['perp_to_par'].append(v_k_par.norm().item())
        norms['perp_to_perp'].append(v_k_perp.norm().item())
    
    return {k: np.max(v) if v else 0.0 for k, v in norms.items()}


def block_row_sum(tensor):
    row_par = tensor['par_to_par'] + tensor['perp_to_par']
    row_perp = tensor['par_to_perp'] + tensor['perp_to_perp']
    return max(row_par, row_perp)


def evaluate_accuracy(model, puzzles, solutions, T, alpha, beta):
    """Evaluate solved accuracy with triangular controller."""
    model.eval()
    correct = 0
    total = 0
    
    with torch.no_grad():
        for i in range(len(puzzles)):
            puzzle = puzzles[i:i+1]
            solution = solutions[i:i+1]
            x_enc = model.encode_puzzle(puzzle)
            z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
            
            # Run triangular inference
            for _ in range(T):
                z = triangular_forward_step(model, z, x_enc, alpha, beta)
            
            y = model.to_logits(z + x_enc)
            pred = y.argmax(dim=-1)
            mask = puzzle.squeeze() == 0
            if mask.sum() > 0:
                correct += (pred.squeeze()[mask] == solution.squeeze()[mask]).all().item()
            total += 1
    
    return correct / total if total > 0 else 0.0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--checkpoint', type=str, default='checkpoints/isr_best.pt')
    parser.add_argument('--n_test', type=int, default=100)
    parser.add_argument('--T', type=int, default=30)
    parser.add_argument('--K', type=int, default=100)
    parser.add_argument('--n_probes', type=int, default=20)
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    args = parser.parse_args()
    
    print("="*70)
    print("SGC TRIANGULAR CONTROLLER: Minimal Schur-Complement Intervention")
    print("="*70)
    
    print(f"\n[1/5] Training model (50 epochs for real dynamics)...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        1000, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long).to(args.device)
    solutions = torch.tensor(solutions, dtype=torch.long).to(args.device)
    
    model = ISRSolver(64, 1).to(args.device)
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)
    batch_size = 64
    
    for epoch in range(1, 51):
        model.train()
        total_loss = 0
        for i in range(0, len(puzzles), batch_size):
            batch_p = puzzles[i:i+batch_size]
            batch_s = solutions[i:i+batch_size]
            optimizer.zero_grad()
            result = model(batch_p, T=30)
            loss = model.compute_loss(result['y_final'], batch_s, batch_p)
            loss.backward()
            optimizer.step()
            total_loss += loss.item()
        if epoch % 10 == 0:
            model.eval()
            with torch.no_grad():
                out = model(puzzles[:100], T=30)
                acc = model.compute_accuracy(out['y_final'], solutions[:100], puzzles[:100])
            print(f"  Epoch {epoch}: loss={total_loss/(len(puzzles)//batch_size):.4f}, solved={acc['solved_acc']*100:.1f}%")
            model.train()
    
    model.eval()
    
    print(f"[2/5] Generating test puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.n_test, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long).to(args.device)
    solutions = torch.tensor(solutions, dtype=torch.long).to(args.device)
    
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzles[:1])
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
    
    print(f"\n[3/5] Baseline: Scalar KM at alpha=0.1...")
    tensor_baseline = measure_block_tensor(model, z, x_enc, K=args.K, alpha=0.1, beta=0.0, n_probes=args.n_probes)
    row_baseline = block_row_sum(tensor_baseline)
    print(f"  par->perp (the pump): {tensor_baseline['par_to_perp']:.3f}")
    print(f"  Row sum: {row_baseline:.3f}")
    
    print(f"\n[4/5] Scanning beta (Schur compensation)...")
    print(f"\n  | beta   | par->perp | perp->perp | row_sum |")
    print(f"  |--------|-----------|------------|---------|")
    
    best_beta = 0.0
    best_row_sum = row_baseline
    
    for beta in [-0.30, -0.25, -0.20, -0.15, -0.10, -0.05, 0.0, 0.05, 0.10, 0.15, 0.20]:
        tensor = measure_block_tensor(model, z, x_enc, K=args.K, alpha=0.1, beta=beta, n_probes=args.n_probes)
        row_sum = block_row_sum(tensor)
        
        marker = ""
        if row_sum < best_row_sum:
            best_row_sum = row_sum
            best_beta = beta
            marker = " <-- best"
        if row_sum < 1.0:
            marker = " *** CONTRACTIVE ***"
        
        print(f"  | {beta:6.2f} | {tensor['par_to_perp']:9.3f} | {tensor['perp_to_perp']:10.3f} | {row_sum:7.3f} |{marker}")
    
    print(f"\n  Best beta: {best_beta:.2f} -> row_sum = {best_row_sum:.3f}")
    
    if best_row_sum < 1.0:
        print(f"\n  *** BREAKTHROUGH: Block-inf contractivity achieved! ***")
    
    print(f"\n[5/5] Evaluating accuracy...")
    acc_undamped = evaluate_accuracy(model, puzzles, solutions, T=args.T, alpha=1.0, beta=0.0)
    acc_scalar = evaluate_accuracy(model, puzzles, solutions, T=args.T, alpha=0.1, beta=0.0)
    acc_tri = evaluate_accuracy(model, puzzles, solutions, T=args.T, alpha=0.1, beta=best_beta)
    
    print(f"\n  Accuracy (T={args.T}):")
    print(f"    Undamped:    {acc_undamped*100:.1f}%")
    print(f"    Scalar KM:   {acc_scalar*100:.1f}%")
    print(f"    Triangular:  {acc_tri*100:.1f}%")
    
    print("\n" + "="*70)
    print("RESULT")
    print("="*70)
    if best_row_sum < 1.0:
        print(f"  Triangular controller (beta={best_beta:.2f}) achieves TRUE CONTRACTIVITY")
        print(f"  This is the minimal Schur-complement intervention that scalar KM cannot reach.")
    else:
        print(f"  Triangular reduces row_sum: {row_baseline:.3f} -> {best_row_sum:.3f}")
        if acc_tri > acc_scalar:
            print(f"  AND improves accuracy: {acc_scalar*100:.1f}% -> {acc_tri*100:.1f}%")


if __name__ == '__main__':
    main()
