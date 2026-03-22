#!/usr/bin/env python3
"""
SGC Anisotropic Fine-Tuning

Fine-tune a pre-trained model with Pi-split dissipation:
    L_diss = lambda_parallel * ||Pi dz||^2 + lambda_perp * ||(I-Pi) dz||^2

Key insight from diagnostic:
- Vertical/Horizontal ratio ~0.5 (both significant)
- Use balanced dissipation, but emphasize late-time steps (last K)

Protocol:
1. Load/train a "hot checkpoint" (model that solves at T=30)
2. Fine-tune with late-time dissipation (last K=50 steps only)
3. Validate: Solved@200 should improve WITHOUT inference damping

Author: SGC Project
"""

import argparse
import numpy as np
import torch
import torch.nn.functional as F
from pathlib import Path
from tqdm import tqdm
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.iterative_spectral_refinement import (
    ISRSolver, SudokuDataset
)

try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


def forward_with_anisotropic_dissipation(model, puzzles, T, K_late, x_enc=None):
    """Forward pass tracking Pi-split velocities for late-time dissipation.
    
    Returns:
        y_final: Final logits
        dissipation_parallel: Sum of ||Pi dz||^2 over last K steps
        dissipation_perp: Sum of ||(I-Pi) dz||^2 over last K steps
    """
    B = puzzles.shape[0]
    device = puzzles.device
    
    if x_enc is None:
        x_enc = model.encode_puzzle(puzzles)
    
    z_t = model.z_init.unsqueeze(0).unsqueeze(0).expand(B, 81, -1).clone()
    
    dissipation_parallel = 0.0
    dissipation_perp = 0.0
    
    for t in range(T):
        z_prev = z_t
        y_t, z_t = model.forward_step(z_t, x_enc)
        
        # Only compute dissipation for last K steps
        if t >= T - K_late:
            delta_z = z_t - z_prev
            
            # Pi-split
            pi_delta_z = model.Pi(delta_z)
            perp_delta_z = delta_z - pi_delta_z
            
            # Squared norms (mean over batch and cells)
            dissipation_parallel = dissipation_parallel + (pi_delta_z ** 2).sum(dim=-1).mean()
            dissipation_perp = dissipation_perp + (perp_delta_z ** 2).sum(dim=-1).mean()
    
    y_final = model.to_logits(z_t + x_enc)
    
    return y_final, dissipation_parallel / K_late, dissipation_perp / K_late


def finetune_epoch(model, loader, opt, epoch, cfg, device):
    """Fine-tuning epoch with anisotropic dissipation."""
    model.train()
    pbar = tqdm(loader, desc=f"Finetune {epoch}")
    
    total_loss = 0
    total_task = 0
    total_diss = 0
    n_batches = 0
    
    for puzzles, solutions in pbar:
        puzzles, solutions = puzzles.to(device), solutions.to(device)
        
        # Forward with dissipation tracking
        y_final, diss_par, diss_perp = forward_with_anisotropic_dissipation(
            model, puzzles, T=cfg['T'], K_late=cfg['K_late']
        )
        
        # Task loss
        task_loss = model.compute_loss(y_final, solutions, puzzles)
        
        # Anisotropic dissipation loss
        diss_loss = cfg['lambda_parallel'] * diss_par + cfg['lambda_perp'] * diss_perp
        
        # Combined
        loss = task_loss + diss_loss
        
        opt.zero_grad()
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        
        total_loss += loss.item()
        total_task += task_loss.item()
        total_diss += diss_loss.item()
        n_batches += 1
        
        # Accuracy
        with torch.no_grad():
            acc = model.compute_accuracy(y_final, solutions, puzzles)
        
        pbar.set_postfix({
            'Loss': f'{loss.item():.4f}',
            'Task': f'{task_loss.item():.4f}',
            'Diss': f'{diss_loss.item():.4f}',
            'Solved': f'{acc["solved_acc"]*100:.1f}%'
        })
    
    return {
        'loss': total_loss / n_batches,
        'task': total_task / n_batches,
        'diss': total_diss / n_batches,
    }


def evaluate(model, puzzles, solutions, T, device, damping_alpha=1.0):
    """Evaluate at given T with optional damping."""
    model.eval()
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    with torch.no_grad():
        result = model(puzzles, T=T, damping_alpha=damping_alpha)
        acc = model.compute_accuracy(result['y_final'], solutions, puzzles)
    
    return {
        'solved': acc['solved_acc'],
        'cell': acc['cell_acc'],
        'violations': acc['violations']['total_violations'],
    }


def main():
    parser = argparse.ArgumentParser(description="SGC Anisotropic Fine-Tuning")
    parser.add_argument('--num_puzzles', type=int, default=3000)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--pretrain_epochs', type=int, default=50)
    parser.add_argument('--finetune_epochs', type=int, default=20)
    parser.add_argument('--T_pretrain', type=int, default=30)
    parser.add_argument('--T_finetune', type=int, default=100, help='Shorter than eval for speed')
    parser.add_argument('--T_eval', type=int, default=200)
    parser.add_argument('--K_late', type=int, default=30, help='Last K steps for dissipation')
    parser.add_argument('--lambda_parallel', type=float, default=0.5)
    parser.add_argument('--lambda_perp', type=float, default=0.5)
    parser.add_argument('--lr_pretrain', type=float, default=1e-3)
    parser.add_argument('--lr_finetune', type=float, default=1e-4, help='Lower LR for fine-tune')
    parser.add_argument('--batch_size', type=int, default=64)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Anisotropic Fine-Tune] Device: {device}")
    print(f"  lambda_parallel: {args.lambda_parallel}")
    print(f"  lambda_perp: {args.lambda_perp}")
    print(f"  K_late: {args.K_late}")
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate puzzles
    print(f"\n[1/4] Generating {args.num_puzzles} puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    n_train = int(0.8 * len(puzzles))
    train_puzzles, test_puzzles = puzzles[:n_train], puzzles[n_train:]
    train_solutions, test_solutions = solutions[:n_train], solutions[n_train:]
    
    train_dataset = torch.utils.data.TensorDataset(train_puzzles, train_solutions)
    train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    
    # Phase 1: Pre-train normally
    print(f"\n[2/4] Phase 1: Pre-training for {args.pretrain_epochs} epochs (T={args.T_pretrain})...")
    model = ISRSolver(args.hidden_dim, args.num_blocks).to(device)
    opt_pretrain = torch.optim.Adam(model.parameters(), lr=args.lr_pretrain)
    
    for epoch in range(1, args.pretrain_epochs + 1):
        model.train()
        total_loss = 0
        n_batches = 0
        
        for p_batch, s_batch in train_loader:
            p_batch, s_batch = p_batch.to(device), s_batch.to(device)
            result = model(p_batch, T=args.T_pretrain)
            loss = model.compute_loss(result['y_final'], s_batch, p_batch)
            
            opt_pretrain.zero_grad()
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            opt_pretrain.step()
            
            total_loss += loss.item()
            n_batches += 1
        
        if epoch % 10 == 0:
            eval_30 = evaluate(model, test_puzzles[:200], test_solutions[:200], T=30, device=device)
            print(f"  Epoch {epoch}: loss={total_loss/n_batches:.4f}, solved@30={eval_30['solved']*100:.1f}%")
    
    # Check baseline before fine-tuning
    print("\n  Pre-train complete. Baseline evaluation:")
    baseline_30 = evaluate(model, test_puzzles, test_solutions, T=30, device=device)
    baseline_200 = evaluate(model, test_puzzles, test_solutions, T=200, device=device)
    baseline_200_damped = evaluate(model, test_puzzles, test_solutions, T=200, device=device, damping_alpha=0.1)
    
    print(f"    T=30:  Solved={baseline_30['solved']*100:.1f}%")
    print(f"    T=200 (no damp): Solved={baseline_200['solved']*100:.1f}%, Viols={baseline_200['violations']:.1f}")
    print(f"    T=200 (damped):  Solved={baseline_200_damped['solved']*100:.1f}%")
    
    # Phase 2: Fine-tune with anisotropic dissipation
    print(f"\n[3/4] Phase 2: Fine-tuning for {args.finetune_epochs} epochs with anisotropic dissipation...")
    opt_finetune = torch.optim.Adam(model.parameters(), lr=args.lr_finetune)
    
    cfg = {
        'T': args.T_finetune,
        'K_late': args.K_late,
        'lambda_parallel': args.lambda_parallel,
        'lambda_perp': args.lambda_perp,
    }
    
    for epoch in range(1, args.finetune_epochs + 1):
        metrics = finetune_epoch(model, train_loader, opt_finetune, epoch, cfg, device)
        
        if epoch % 5 == 0 or epoch == args.finetune_epochs:
            eval_200 = evaluate(model, test_puzzles[:200], test_solutions[:200], T=200, device=device)
            print(f"\n  [Eval] Epoch {epoch}: Solved@200={eval_200['solved']*100:.1f}%, Viols={eval_200['violations']:.1f}")
    
    # Final evaluation
    print("\n" + "="*70)
    print("[4/4] FINAL EVALUATION")
    print("="*70)
    
    final_30 = evaluate(model, test_puzzles, test_solutions, T=30, device=device)
    final_200 = evaluate(model, test_puzzles, test_solutions, T=200, device=device)
    final_200_damped = evaluate(model, test_puzzles, test_solutions, T=200, device=device, damping_alpha=0.1)
    
    print(f"\nAfter fine-tuning:")
    print(f"  T=30:  Solved={final_30['solved']*100:.1f}%")
    print(f"  T=200 (no damp): Solved={final_200['solved']*100:.1f}%, Viols={final_200['violations']:.1f}")
    print(f"  T=200 (damped):  Solved={final_200_damped['solved']*100:.1f}%")
    
    print(f"\nComparison (T=200, no damping):")
    print(f"  Before fine-tune: {baseline_200['solved']*100:.1f}%")
    print(f"  After fine-tune:  {final_200['solved']*100:.1f}%")
    
    improvement = final_200['solved'] - baseline_200['solved']
    
    print("\n" + "="*70)
    print("SGC VERDICT")
    print("="*70)
    
    if final_200['solved'] > 0.3:
        print(f"\n[SUCCESS] Anisotropic dissipation works!")
        print(f"  Achieved {final_200['solved']*100:.1f}% solved at T=200 WITHOUT inference damping")
        print(f"  The SGC-guided friction tensor creates stable attractors.")
    elif improvement > 0.05:
        print(f"\n[PARTIAL] Some improvement ({improvement*100:.1f}%), but needs more tuning")
        print(f"  Try: different lambda values, more epochs, or Jacobian regularization")
    else:
        print(f"\n[NEEDS WORK] Fine-tuning didn't help significantly")
        print(f"  Consider: Jacobian spectral radius control (DEQ-style)")
    
    # Plot
    if MATPLOTLIB_AVAILABLE:
        fig, ax = plt.subplots(1, 1, figsize=(8, 6))
        
        conditions = ['T=30', 'T=200\n(no damp)', 'T=200\n(damped)']
        before = [baseline_30['solved']*100, baseline_200['solved']*100, baseline_200_damped['solved']*100]
        after = [final_30['solved']*100, final_200['solved']*100, final_200_damped['solved']*100]
        
        x = np.arange(len(conditions))
        width = 0.35
        
        bars1 = ax.bar(x - width/2, before, width, label='Before Fine-tune', color='lightcoral')
        bars2 = ax.bar(x + width/2, after, width, label='After Fine-tune', color='lightgreen')
        
        ax.set_ylabel('Solved Accuracy (%)')
        ax.set_title('Effect of Anisotropic Fine-Tuning')
        ax.set_xticks(x)
        ax.set_xticklabels(conditions)
        ax.legend()
        ax.set_ylim(0, 100)
        ax.grid(True, alpha=0.3, axis='y')
        
        # Value labels
        for bar in bars1:
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 1,
                   f'{bar.get_height():.1f}', ha='center', va='bottom', fontsize=9)
        for bar in bars2:
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 1,
                   f'{bar.get_height():.1f}', ha='center', va='bottom', fontsize=9)
        
        plt.tight_layout()
        plt.savefig('logs/sgc_anisotropic_finetune.png', dpi=150)
        print(f"\nPlot saved to logs/sgc_anisotropic_finetune.png")
        plt.close()


if __name__ == '__main__':
    main()
