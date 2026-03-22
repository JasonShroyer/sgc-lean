#!/usr/bin/env python3
"""
SGC Defect-Aware Training Experiment

The Causal Test:
- SGC theory claims: low defect D = (I-Pi)F(Pi(z)) -> macro-coherence -> high accuracy
- This experiment tests that claim by comparing:
  1. Standard training: CE loss only
  2. Defect training: CE loss + lambda * defect_loss

If defect training leads to:
  - Lower block row-sum (better stability)
  - Higher accuracy (better task performance)
Then we have CAUSAL evidence that SGC math links to performance.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
import sys
import os
import argparse

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from iterative_spectral_refinement import ISRSolver, SudokuDataset
from sudoku_data_utils import load_or_generate


def measure_block_tensor(model, puzzles, solutions, K=30, n_probes=20):
    """Measure K-step block operator norms."""
    model.eval()
    device = next(model.parameters()).device
    
    # Use a subset for measurement
    n = min(20, len(puzzles))
    puzzles = puzzles[:n].to(device)
    x_enc = model.encode_puzzle(puzzles)
    
    with torch.no_grad():
        # Get initial state
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(n, 81, -1).clone()
        
        # Run a few steps to get to interesting regime
        for _ in range(5):
            _, z = model.forward_step(z, x_enc)
    
    D = z.shape[-1]
    
    def apply_K_steps(z_in):
        z_cur = z_in.clone()
        with torch.no_grad():
            for _ in range(K):
                _, z_cur = model.forward_step(z_cur, x_enc)
        return z_cur
    
    # Measure block norms via probing
    norms = {'par_to_par': 0, 'par_to_perp': 0, 'perp_to_par': 0, 'perp_to_perp': 0}
    
    for _ in range(n_probes):
        # Random probe in par subspace
        v_rand = torch.randn_like(z)
        v_par = model.Pi(v_rand)
        v_par = v_par / (v_par.norm() + 1e-8)
        
        z_pert = z + 0.01 * v_par
        z_out = apply_K_steps(z_pert)
        delta = (z_out - apply_K_steps(z)) / 0.01
        
        delta_par = model.Pi(delta)
        delta_perp = delta - delta_par
        
        norms['par_to_par'] = max(norms['par_to_par'], delta_par.norm().item())
        norms['par_to_perp'] = max(norms['par_to_perp'], delta_perp.norm().item())
        
        # Random probe in perp subspace
        v_perp = v_rand - model.Pi(v_rand)
        v_perp = v_perp / (v_perp.norm() + 1e-8)
        
        z_pert = z + 0.01 * v_perp
        z_out = apply_K_steps(z_pert)
        delta = (z_out - apply_K_steps(z)) / 0.01
        
        delta_par = model.Pi(delta)
        delta_perp = delta - delta_par
        
        norms['perp_to_par'] = max(norms['perp_to_par'], delta_par.norm().item())
        norms['perp_to_perp'] = max(norms['perp_to_perp'], delta_perp.norm().item())
    
    norms['row_sum'] = max(
        norms['par_to_par'] + norms['par_to_perp'],
        norms['perp_to_par'] + norms['perp_to_perp']
    )
    
    return norms


def train_model(model, puzzles, solutions, epochs, defect_lambda=0.0, device='cpu'):
    """Train model with optional defect regularization."""
    model.train()
    optimizer = optim.Adam(model.parameters(), lr=1e-3)
    
    history = {'ce_loss': [], 'defect_loss': [], 'accuracy': []}
    
    for epoch in range(epochs):
        total_ce = 0
        total_defect = 0
        total_correct = 0
        total_puzzles = 0
        
        # Mini-batch training
        batch_size = 32
        indices = torch.randperm(len(puzzles))
        
        for i in range(0, len(puzzles), batch_size):
            batch_idx = indices[i:i+batch_size]
            batch_puzzles = puzzles[batch_idx].to(device)
            batch_solutions = solutions[batch_idx].to(device)
            
            optimizer.zero_grad()
            
            if defect_lambda > 0:
                # Forward with defect tracking
                out = model(batch_puzzles, T=30, return_defect=True)
                ce_loss = model.compute_loss(out['y_final'], batch_solutions, batch_puzzles)
                defect_loss, _ = model.compute_defect_loss(out['defect_traj'])
                loss = ce_loss + defect_lambda * defect_loss
                total_defect += defect_loss.item() * len(batch_idx)
            else:
                # Standard forward
                out = model(batch_puzzles, T=30)
                ce_loss = model.compute_loss(out['y_final'], batch_solutions, batch_puzzles)
                loss = ce_loss
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
            
            total_ce += ce_loss.item() * len(batch_idx)
            
            # Accuracy
            with torch.no_grad():
                acc = model.compute_accuracy(out['y_final'], batch_solutions, batch_puzzles)
                total_correct += acc['solved_acc'] * len(batch_idx)
            total_puzzles += len(batch_idx)
        
        avg_ce = total_ce / total_puzzles
        avg_defect = total_defect / total_puzzles if defect_lambda > 0 else 0
        avg_acc = total_correct / total_puzzles
        
        history['ce_loss'].append(avg_ce)
        history['defect_loss'].append(avg_defect)
        history['accuracy'].append(avg_acc)
        
        if (epoch + 1) % 10 == 0:
            tag = f"[D={defect_lambda}]" if defect_lambda > 0 else "[std]"
            print(f"  {tag} Epoch {epoch+1}: CE={avg_ce:.4f}, Defect={avg_defect:.4f}, Acc={avg_acc*100:.1f}%")
    
    return history


def evaluate_model(model, puzzles, solutions, device='cpu'):
    """Evaluate model accuracy."""
    model.eval()
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    with torch.no_grad():
        out = model(puzzles, T=30)
        acc = model.compute_accuracy(out['y_final'], solutions, puzzles)
        
        # Also measure commutator defect
        out_defect = model(puzzles[:20], T=30, return_defect=True)
        _, defect_metrics = model.compute_defect_loss(out_defect['defect_traj'])
    
    return {
        'solved_acc': acc['solved_acc'],
        'cell_acc': acc['cell_acc'],
        'defect_final': defect_metrics['defect_final'],
        'defect_mean': defect_metrics['defect_mean'],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n_train', type=int, default=2000)
    parser.add_argument('--n_test', type=int, default=100)
    parser.add_argument('--epochs', type=int, default=100)
    parser.add_argument('--defect_lambda', type=float, default=0.1)
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    parser.add_argument('--K', type=int, default=30, help='Block norm horizon')
    args = parser.parse_args()
    
    print("="*70)
    print("SGC DEFECT-AWARE TRAINING EXPERIMENT")
    print("="*70)
    print(f"Config: {args.n_train} train, {args.epochs} epochs, defect_lambda={args.defect_lambda}")
    print()
    
    # Fast data loading (cached or generated without uniqueness)
    train_puzzles, train_solutions = load_or_generate(
        args.n_train, cache_dir='data/sudoku_cache', seed=42, split='train')
    test_puzzles, test_solutions = load_or_generate(
        args.n_test, cache_dir='data/sudoku_cache', seed=123, split='test')
    
    train_puzzles = torch.tensor(train_puzzles, dtype=torch.long)
    train_solutions = torch.tensor(train_solutions, dtype=torch.long)
    test_puzzles = torch.tensor(test_puzzles, dtype=torch.long)
    test_solutions = torch.tensor(test_solutions, dtype=torch.long)
    
    # Create two models with same initialization
    torch.manual_seed(42)
    model_std = ISRSolver(hidden_dim=64, num_blocks=4).to(args.device)
    
    torch.manual_seed(42)
    model_defect = ISRSolver(hidden_dim=64, num_blocks=4).to(args.device)
    
    print(f"Model parameters: {sum(p.numel() for p in model_std.parameters()):,}")
    print()
    
    # Train standard model
    print("="*70)
    print("PHASE 1: Training STANDARD model (CE loss only)")
    print("="*70)
    history_std = train_model(model_std, train_puzzles, train_solutions, 
                              args.epochs, defect_lambda=0.0, device=args.device)
    
    # Train defect-regularized model
    print()
    print("="*70)
    print(f"PHASE 2: Training DEFECT model (CE + {args.defect_lambda}*defect)")
    print("="*70)
    history_defect = train_model(model_defect, train_puzzles, train_solutions,
                                  args.epochs, defect_lambda=args.defect_lambda, device=args.device)
    
    # Evaluate both
    print()
    print("="*70)
    print("PHASE 3: Evaluation on test set")
    print("="*70)
    
    eval_std = evaluate_model(model_std, test_puzzles, test_solutions, args.device)
    eval_defect = evaluate_model(model_defect, test_puzzles, test_solutions, args.device)
    
    print(f"\n  STANDARD model:")
    print(f"    Solved accuracy: {eval_std['solved_acc']*100:.1f}%")
    print(f"    Cell accuracy:   {eval_std['cell_acc']*100:.1f}%")
    print(f"    Final defect:    {eval_std['defect_final']:.4f}")
    
    print(f"\n  DEFECT model:")
    print(f"    Solved accuracy: {eval_defect['solved_acc']*100:.1f}%")
    print(f"    Cell accuracy:   {eval_defect['cell_acc']*100:.1f}%")
    print(f"    Final defect:    {eval_defect['defect_final']:.4f}")
    
    # Measure block tensors
    print()
    print("="*70)
    print(f"PHASE 4: Block tensor measurement (K={args.K})")
    print("="*70)
    
    norms_std = measure_block_tensor(model_std, test_puzzles, test_solutions, K=args.K)
    norms_defect = measure_block_tensor(model_defect, test_puzzles, test_solutions, K=args.K)
    
    print(f"\n  STANDARD model block norms:")
    print(f"    par->par:   {norms_std['par_to_par']:.1f}")
    print(f"    par->perp:  {norms_std['par_to_perp']:.1f}  <- PUMP")
    print(f"    perp->par:  {norms_std['perp_to_par']:.1f}")
    print(f"    perp->perp: {norms_std['perp_to_perp']:.1f}")
    print(f"    Row-sum:    {norms_std['row_sum']:.1f}")
    
    print(f"\n  DEFECT model block norms:")
    print(f"    par->par:   {norms_defect['par_to_par']:.1f}")
    print(f"    par->perp:  {norms_defect['par_to_perp']:.1f}  <- PUMP")
    print(f"    perp->par:  {norms_defect['perp_to_par']:.1f}")
    print(f"    perp->perp: {norms_defect['perp_to_perp']:.1f}")
    print(f"    Row-sum:    {norms_defect['row_sum']:.1f}")
    
    # Summary
    print()
    print("="*70)
    print("CAUSAL TEST SUMMARY")
    print("="*70)
    
    acc_delta = (eval_defect['solved_acc'] - eval_std['solved_acc']) * 100
    defect_delta = eval_defect['defect_final'] - eval_std['defect_final']
    pump_delta = norms_defect['par_to_perp'] - norms_std['par_to_perp']
    rowsum_delta = norms_defect['row_sum'] - norms_std['row_sum']
    
    print(f"\n  Defect training effect:")
    print(f"    Accuracy change:    {acc_delta:+.1f}%")
    print(f"    Final defect change: {defect_delta:+.4f}")
    print(f"    Pump change:         {pump_delta:+.1f}")
    print(f"    Row-sum change:      {rowsum_delta:+.1f}")
    
    if acc_delta > 0 and defect_delta < 0:
        print(f"\n  >> SGC VALIDATED: Lower defect -> Higher accuracy")
    elif acc_delta > 0:
        print(f"\n  >> Accuracy improved but defect didn't decrease - need investigation")
    elif defect_delta < 0:
        print(f"\n  >> Defect decreased but accuracy didn't improve - closure != performance?")
    else:
        print(f"\n  >> No clear improvement - defect regularization may need tuning")
    
    # Save models
    os.makedirs('checkpoints', exist_ok=True)
    torch.save({
        'model_state': model_std.state_dict(),
        'history': history_std,
        'eval': eval_std,
        'block_norms': norms_std,
    }, 'checkpoints/model_standard.pt')
    
    torch.save({
        'model_state': model_defect.state_dict(),
        'history': history_defect,
        'eval': eval_defect,
        'block_norms': norms_defect,
    }, 'checkpoints/model_defect.pt')
    
    print(f"\n  Models saved to checkpoints/")


if __name__ == '__main__':
    main()
