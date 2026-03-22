#!/usr/bin/env python3
"""
SGC Unified Experiment Pipeline
================================
Proper pipeline that:
1. Trains model to reasonable performance (>30% solved)
2. SAVES checkpoint for reproducibility
3. Measures block tensor on trained model
4. Tests controllers on the SAME checkpoint

This ensures all comparisons are on identical dynamics.
"""

import torch
import torch.nn as nn
import numpy as np
import argparse
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))
from demos.iterative_spectral_refinement import ISRSolver, SudokuDataset


def train_and_save(args):
    """Train model until reasonable performance, then save."""
    print("\n" + "="*70)
    print("PHASE 1: Training to convergence")
    print("="*70)
    
    # Generate training data
    print(f"\nGenerating {args.n_train} training puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.n_train, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long).to(args.device)
    solutions = torch.tensor(solutions, dtype=torch.long).to(args.device)
    
    model = ISRSolver(64, 1).to(args.device)
    optimizer = torch.optim.Adam(model.parameters(), lr=1e-3)
    scheduler = torch.optim.lr_scheduler.ReduceLROnPlateau(optimizer, patience=20, factor=0.5)
    batch_size = 64
    
    best_acc = 0.0
    patience_counter = 0
    
    for epoch in range(1, args.max_epochs + 1):
        model.train()
        total_loss = 0
        n_batches = 0
        
        # Shuffle
        perm = torch.randperm(len(puzzles))
        puzzles = puzzles[perm]
        solutions = solutions[perm]
        
        for i in range(0, len(puzzles), batch_size):
            batch_p = puzzles[i:i+batch_size]
            batch_s = solutions[i:i+batch_size]
            optimizer.zero_grad()
            result = model(batch_p, T=30)
            loss = model.compute_loss(result['y_final'], batch_s, batch_p)
            loss.backward()
            optimizer.step()
            total_loss += loss.item()
            n_batches += 1
        
        avg_loss = total_loss / n_batches
        scheduler.step(avg_loss)
        
        # Evaluate every 10 epochs
        if epoch % 10 == 0:
            model.eval()
            with torch.no_grad():
                out = model(puzzles[:200], T=30)
                acc = model.compute_accuracy(out['y_final'], solutions[:200], puzzles[:200])
            solved = acc['solved_acc'] * 100
            print(f"  Epoch {epoch:3d}: loss={avg_loss:.4f}, solved={solved:.1f}%, lr={optimizer.param_groups[0]['lr']:.1e}")
            
            if solved > best_acc:
                best_acc = solved
                patience_counter = 0
                # Save best checkpoint
                torch.save({
                    'epoch': epoch,
                    'model_state_dict': model.state_dict(),
                    'optimizer_state_dict': optimizer.state_dict(),
                    'solved_acc': solved,
                    'loss': avg_loss,
                }, args.checkpoint_path)
                print(f"    -> Saved checkpoint (best so far)")
            else:
                patience_counter += 1
            
            # Early stopping if good enough or stalled
            if solved >= args.target_acc:
                print(f"\n  Reached target accuracy {args.target_acc}%!")
                break
            if patience_counter >= args.patience:
                print(f"\n  Early stopping (no improvement for {args.patience} eval cycles)")
                break
    
    print(f"\nBest accuracy achieved: {best_acc:.1f}%")
    print(f"Checkpoint saved to: {args.checkpoint_path}")
    return model, best_acc


def load_checkpoint(args):
    """Load saved checkpoint."""
    if not os.path.exists(args.checkpoint_path):
        raise FileNotFoundError(f"No checkpoint at {args.checkpoint_path}. Run with --train first.")
    
    model = ISRSolver(64, 1).to(args.device)
    checkpoint = torch.load(args.checkpoint_path, map_location=args.device)
    model.load_state_dict(checkpoint['model_state_dict'])
    print(f"Loaded checkpoint: epoch={checkpoint['epoch']}, solved={checkpoint['solved_acc']:.1f}%")
    return model, checkpoint['solved_acc']


def measure_block_tensor(model, z, x_enc, K, alpha, beta=0.0, n_probes=20):
    """Measure 2x2 restricted block tensor via finite differences.
    
    If beta != 0, uses triangular controller dynamics.
    """
    device = z.device
    eps = 1e-4
    
    def apply_K_steps(z_in):
        z_cur = z_in.clone()
        for _ in range(K):
            _, z_next = model.forward_step(z_cur, x_enc)
            u = z_next - z_cur
            u_par = model.Pi(u)
            u_perp = u - u_par
            # Triangular controller: dz_perp -= beta * u_par
            dz_par = alpha * u_par
            dz_perp = alpha * u_perp - beta * u_par
            z_cur = z_cur + dz_par + dz_perp
        return z_cur
    
    norms = {'par_to_par': [], 'par_to_perp': [], 'perp_to_par': [], 'perp_to_perp': []}
    
    for _ in range(n_probes):
        # Random probe in par subspace
        v_full = torch.randn_like(z)
        v_par = model.Pi(v_full)
        v_par = v_par / (v_par.norm() + 1e-8) * eps
        
        z_plus = apply_K_steps(z + v_par)
        z_minus = apply_K_steps(z - v_par)
        Jv = (z_plus - z_minus) / (2 * eps)
        
        Jv_par = model.Pi(Jv)
        Jv_perp = Jv - Jv_par
        
        norms['par_to_par'].append(Jv_par.norm().item() / (v_par.norm().item() + 1e-8))
        norms['par_to_perp'].append(Jv_perp.norm().item() / (v_par.norm().item() + 1e-8))
        
        # Random probe in perp subspace
        v_perp = v_full - model.Pi(v_full)
        v_perp = v_perp / (v_perp.norm() + 1e-8) * eps
        
        z_plus = apply_K_steps(z + v_perp)
        z_minus = apply_K_steps(z - v_perp)
        Jv = (z_plus - z_minus) / (2 * eps)
        
        Jv_par = model.Pi(Jv)
        Jv_perp = Jv - Jv_par
        
        norms['perp_to_par'].append(Jv_par.norm().item() / (v_perp.norm().item() + 1e-8))
        norms['perp_to_perp'].append(Jv_perp.norm().item() / (v_perp.norm().item() + 1e-8))
    
    return {k: np.max(v) for k, v in norms.items()}


def triangular_forward_step(model, z, x_enc, alpha, beta):
    """Triangular controller: Δz_perp -= β * u_par"""
    _, z_next = model.forward_step(z, x_enc)
    u = z_next - z
    u_par = model.Pi(u)
    u_perp = u - u_par
    
    dz_par = alpha * u_par
    dz_perp = alpha * u_perp - beta * u_par
    
    return z + dz_par + dz_perp


def evaluate_accuracy(model, puzzles, solutions, T, alpha, beta):
    """Evaluate solved accuracy with triangular controller."""
    correct = 0
    with torch.no_grad():
        for i in range(len(puzzles)):
            puzzle = puzzles[i:i+1]
            solution = solutions[i:i+1]
            x_enc = model.encode_puzzle(puzzle)
            z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
            
            for _ in range(T):
                z = triangular_forward_step(model, z, x_enc, alpha, beta)
            
            y = model.to_logits(z + x_enc)
            pred = y.argmax(dim=-1)
            mask = puzzle.squeeze() == 0
            if mask.sum() > 0:
                correct += (pred.squeeze()[mask] == solution.squeeze()[mask]).all().item()
    
    return correct / len(puzzles)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--train', action='store_true', help='Train new model')
    parser.add_argument('--n_train', type=int, default=2000)
    parser.add_argument('--n_test', type=int, default=100)
    parser.add_argument('--max_epochs', type=int, default=200)
    parser.add_argument('--target_acc', type=float, default=50.0)
    parser.add_argument('--patience', type=int, default=10)
    parser.add_argument('--K', type=int, default=100)
    parser.add_argument('--n_probes', type=int, default=30)
    parser.add_argument('--checkpoint_path', type=str, default='checkpoints/isr_trained.pt')
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    args = parser.parse_args()
    
    # Ensure checkpoint directory exists
    os.makedirs(os.path.dirname(args.checkpoint_path), exist_ok=True)
    
    # Phase 1: Train or load
    if args.train:
        model, train_acc = train_and_save(args)
    else:
        model, train_acc = load_checkpoint(args)
    
    model.eval()
    
    # Phase 2: Generate test puzzles
    print("\n" + "="*70)
    print("PHASE 2: Measuring block tensor on SAVED checkpoint")
    print("="*70)
    
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.n_test, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long).to(args.device)
    solutions = torch.tensor(solutions, dtype=torch.long).to(args.device)
    
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzles[:1])
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
    
    # Measure at α=1.0 (undamped) to see true non-normality
    print(f"\nBlock tensor at K={args.K}, alpha=1.0 (undamped):")
    tensor_undamped = measure_block_tensor(model, z, x_enc, K=args.K, alpha=1.0, n_probes=args.n_probes)
    print(f"  par->par:   {tensor_undamped['par_to_par']:.3f}")
    print(f"  par->perp:  {tensor_undamped['par_to_perp']:.3f}  <- THE PUMP")
    print(f"  perp->par:  {tensor_undamped['perp_to_par']:.3f}")
    print(f"  perp->perp: {tensor_undamped['perp_to_perp']:.3f}")
    row_sum_undamped = max(
        tensor_undamped['par_to_par'] + tensor_undamped['perp_to_par'],
        tensor_undamped['par_to_perp'] + tensor_undamped['perp_to_perp']
    )
    print(f"  Block row-sum: {row_sum_undamped:.3f}")
    
    # Measure at α=0.1 (scalar KM)
    print(f"\nBlock tensor at K={args.K}, alpha=0.1 (scalar KM):")
    tensor_km = measure_block_tensor(model, z, x_enc, K=args.K, alpha=0.1, n_probes=args.n_probes)
    print(f"  par->par:   {tensor_km['par_to_par']:.3f}")
    print(f"  par->perp:  {tensor_km['par_to_perp']:.3f}")
    print(f"  perp->par:  {tensor_km['perp_to_par']:.3f}")
    print(f"  perp->perp: {tensor_km['perp_to_perp']:.3f}")
    row_sum_km = max(
        tensor_km['par_to_par'] + tensor_km['perp_to_par'],
        tensor_km['par_to_perp'] + tensor_km['perp_to_perp']
    )
    print(f"  Block row-sum: {row_sum_km:.3f}")
    
    # Phase 3: Test triangular controller (if pump is significant)
    print("\n" + "="*70)
    print("PHASE 3: Triangular controller scan")
    print("="*70)
    
    print(f"\n  | beta   | par->perp | perp->perp | row_sum  | vs KM   |")
    print(f"  |--------|-----------|------------|----------|---------|")
    
    best_beta = 0.0
    best_row_sum = row_sum_km
    
    for beta in [-0.3, -0.2, -0.1, -0.05, 0.0, 0.05, 0.1, 0.2, 0.3]:
        # Measure with triangular dynamics (beta affects the iteration)
        tensor = measure_block_tensor(model, z, x_enc, K=args.K, alpha=0.1, beta=beta, n_probes=args.n_probes)
        row_sum = max(
            tensor['par_to_par'] + tensor['perp_to_par'],
            tensor['par_to_perp'] + tensor['perp_to_perp']
        )
        
        delta = row_sum - row_sum_km
        marker = ""
        if row_sum < best_row_sum:
            best_row_sum = row_sum
            best_beta = beta
            marker = " <- best"
        
        print(f"  | {beta:+.2f}  | {tensor['par_to_perp']:.3f}     | {tensor['perp_to_perp']:.3f}      | {row_sum:.3f}    | {delta:+.3f}  |{marker}")
    
    # Phase 4: Evaluate accuracy using model's built-in damping
    print("\n" + "="*70)
    print("PHASE 4: Accuracy evaluation (using model's built-in forward)")
    print("="*70)
    
    with torch.no_grad():
        # Undamped (alpha=1.0)
        out_undamped = model(puzzles, T=30, damping_alpha=1.0)
        acc_undamped = model.compute_accuracy(out_undamped['y_final'], solutions, puzzles)
        
        # Scan different damping levels
        print(f"\n  Undamped (a=1.0, T=30):  {acc_undamped['solved_acc']*100:.1f}%")
        print(f"\n  Damping scan at T=30:")
        for alpha in [0.9, 0.7, 0.5, 0.3, 0.1]:
            out = model(puzzles, T=30, damping_alpha=alpha)
            acc = model.compute_accuracy(out['y_final'], solutions, puzzles)
            print(f"    a={alpha}: {acc['solved_acc']*100:.1f}%")
        
        print(f"\n  Damping scan at T=100:")
        for alpha in [0.5, 0.3, 0.1]:
            out = model(puzzles, T=100, damping_alpha=alpha)
            acc = model.compute_accuracy(out['y_final'], solutions, puzzles)
            print(f"    a={alpha}: {acc['solved_acc']*100:.1f}%")
    
    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    print(f"  Checkpoint solved accuracy: {train_acc:.1f}%")
    print(f"  Pump channel (a=1.0):       {tensor_undamped['par_to_perp']:.3f}")
    print(f"  Row-sum undamped:           {row_sum_undamped:.3f}")
    print(f"  Row-sum scalar KM:          {row_sum_km:.3f}")
    print(f"  Best triangular beta:       {best_beta:.2f}")
    print(f"  Best triangular row-sum:    {best_row_sum:.3f}")


if __name__ == '__main__':
    main()
