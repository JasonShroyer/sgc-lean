#!/usr/bin/env python3
"""
SGC Damped Training Experiment

Train with KM damping baked in and velocity penalty to create stable attractors.

Based on the damping test results:
- Alpha=0.1 recovered 25.5% solved from 0% at T=200
- This proves correct solutions ARE attractors but were being overshot

This experiment trains with:
1. KM damping (alpha=0.1-0.2) during forward pass
2. Velocity penalty: ||z_{t+1} - z_t||^2 weighted toward late steps
3. Task loss: Cross-entropy on empty cells

Goal: Achieve >50% solved at T=200 with stable convergence.

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


def train_epoch_damped(model, loader, opt, epoch, cfg, device):
    """Training epoch with KM damping and velocity penalty."""
    model.train()
    pbar = tqdm(loader, desc=f"Epoch {epoch}")
    
    total_loss = 0
    total_task_loss = 0
    total_vel_loss = 0
    n_batches = 0
    
    for puzzles, solutions in pbar:
        puzzles, solutions = puzzles.to(device), solutions.to(device)
        
        # Forward with damping and velocity tracking
        result = model(
            puzzles, 
            T=cfg['T'], 
            return_trajectory=True,
            return_velocity=True,
            damping_alpha=cfg['damping_alpha']
        )
        
        # Task loss
        task_loss = model.compute_loss(result['y_final'], solutions, puzzles)
        
        # Velocity penalty (late-time emphasis)
        # Weight later steps more heavily to encourage convergence
        vel_traj = result['velocity_traj']  # (T,)
        T = len(vel_traj)
        # Linear ramp: step t gets weight (t+1)/T
        weights = torch.arange(1, T+1, device=device).float() / T
        weighted_vel = (vel_traj * weights).mean()
        vel_loss = weighted_vel
        
        # Combined loss
        loss = task_loss + cfg['velocity_weight'] * vel_loss
        
        opt.zero_grad()
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        
        total_loss += loss.item()
        total_task_loss += task_loss.item()
        total_vel_loss += vel_loss.item()
        n_batches += 1
        
        # Compute accuracy for display
        with torch.no_grad():
            acc = model.compute_accuracy(result['y_final'], solutions, puzzles)
        
        pbar.set_postfix({
            'Loss': f'{loss.item():.4f}',
            'Task': f'{task_loss.item():.4f}',
            'Vel': f'{vel_loss.item():.4f}',
            'Solved': f'{acc["solved_acc"]*100:.1f}%'
        })
    
    return {
        'loss': total_loss / n_batches,
        'task_loss': total_task_loss / n_batches,
        'vel_loss': total_vel_loss / n_batches,
    }


def evaluate(model, puzzles, solutions, T, damping_alpha, device):
    """Evaluate model with damping."""
    model.eval()
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    with torch.no_grad():
        result = model(
            puzzles, 
            T=T, 
            return_velocity=True,
            damping_alpha=damping_alpha
        )
        
        acc = model.compute_accuracy(result['y_final'], solutions, puzzles)
        
        # Final velocity
        final_vel = result['velocity_traj'][-1].item() if len(result['velocity_traj']) > 0 else 0
        
    return {
        'solved_acc': acc['solved_acc'],
        'cell_acc': acc['cell_acc'],
        'violations': acc['violations']['total_violations'],
        'final_velocity': final_vel,
    }


def main():
    parser = argparse.ArgumentParser(description="SGC Damped Training")
    parser.add_argument('--num_puzzles', type=int, default=5000)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--T_train', type=int, default=30, help='Training steps')
    parser.add_argument('--T_eval', type=int, default=200, help='Evaluation steps')
    parser.add_argument('--epochs', type=int, default=50)
    parser.add_argument('--batch_size', type=int, default=64)
    parser.add_argument('--lr', type=float, default=1e-3)
    parser.add_argument('--damping_alpha', type=float, default=0.15, help='KM damping (0.1-0.2 recommended)')
    parser.add_argument('--velocity_weight', type=float, default=0.1, help='Weight for velocity penalty')
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Damped Training] Device: {device}")
    print(f"  Damping alpha: {args.damping_alpha}")
    print(f"  Velocity weight: {args.velocity_weight}")
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate puzzles
    print(f"\n[1/3] Generating {args.num_puzzles} puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    # Split train/test
    n_train = int(0.8 * len(puzzles))
    train_puzzles, test_puzzles = puzzles[:n_train], puzzles[n_train:]
    train_solutions, test_solutions = solutions[:n_train], solutions[n_train:]
    
    train_dataset = torch.utils.data.TensorDataset(train_puzzles, train_solutions)
    train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    
    # Create model
    print(f"\n[2/3] Training with damping for {args.epochs} epochs...")
    model = ISRSolver(args.hidden_dim, args.num_blocks).to(device)
    optimizer = torch.optim.Adam(model.parameters(), lr=args.lr)
    
    cfg = {
        'T': args.T_train,
        'damping_alpha': args.damping_alpha,
        'velocity_weight': args.velocity_weight,
    }
    
    history = {'train_loss': [], 'solved_T30': [], 'solved_T200': [], 'velocity': []}
    
    for epoch in range(1, args.epochs + 1):
        train_metrics = train_epoch_damped(model, train_loader, optimizer, epoch, cfg, device)
        history['train_loss'].append(train_metrics['loss'])
        
        # Evaluate at T=30 and T=200
        if epoch % 5 == 0 or epoch == args.epochs:
            eval_30 = evaluate(model, test_puzzles[:200], test_solutions[:200], 
                              T=30, damping_alpha=args.damping_alpha, device=device)
            eval_200 = evaluate(model, test_puzzles[:200], test_solutions[:200], 
                               T=200, damping_alpha=args.damping_alpha, device=device)
            
            history['solved_T30'].append(eval_30['solved_acc'])
            history['solved_T200'].append(eval_200['solved_acc'])
            history['velocity'].append(eval_200['final_velocity'])
            
            print(f"\n  [Eval] Epoch {epoch}:")
            print(f"    T=30:  Solved={eval_30['solved_acc']*100:.1f}%, Vel={eval_30['final_velocity']:.4f}")
            print(f"    T=200: Solved={eval_200['solved_acc']*100:.1f}%, Vel={eval_200['final_velocity']:.4f}, Viols={eval_200['violations']:.1f}")
    
    # Final comparison: with vs without damping at inference
    print("\n" + "="*70)
    print("FINAL EVALUATION")
    print("="*70)
    
    print("\nWith damping (alpha={:.2f}):".format(args.damping_alpha))
    eval_damped = evaluate(model, test_puzzles, test_solutions, 
                           T=200, damping_alpha=args.damping_alpha, device=device)
    print(f"  Solved@200: {eval_damped['solved_acc']*100:.1f}%")
    print(f"  Velocity: {eval_damped['final_velocity']:.6f}")
    print(f"  Violations: {eval_damped['violations']:.1f}")
    
    print("\nWithout damping (alpha=1.0):")
    eval_undamped = evaluate(model, test_puzzles, test_solutions, 
                             T=200, damping_alpha=1.0, device=device)
    print(f"  Solved@200: {eval_undamped['solved_acc']*100:.1f}%")
    print(f"  Velocity: {eval_undamped['final_velocity']:.6f}")
    print(f"  Violations: {eval_undamped['violations']:.1f}")
    
    # SGC Success criterion
    print("\n" + "="*70)
    print("SGC SUCCESS CRITERION")
    print("="*70)
    
    if eval_damped['solved_acc'] > 0.5:
        print("[SUCCESS] Achieved >50% solved at T=200 with damped training!")
        print("  The SGC attractor hypothesis is validated:")
        print("  - Correct solutions are stable fixed points")
        print("  - KM damping enables convergence")
    elif eval_damped['solved_acc'] > eval_undamped['solved_acc'] + 0.1:
        print("[PARTIAL] Damping helps but needs more training/tuning")
        print(f"  Improvement: {eval_undamped['solved_acc']*100:.1f}% -> {eval_damped['solved_acc']*100:.1f}%")
    else:
        print("[NEEDS WORK] Damped training not yet effective")
        print("  Consider: different alpha, more epochs, Jacobian regularization")
    
    # Plot
    if MATPLOTLIB_AVAILABLE and len(history['solved_T200']) > 1:
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        
        epochs_eval = list(range(5, args.epochs + 1, 5))
        if args.epochs not in epochs_eval:
            epochs_eval.append(args.epochs)
        
        # Training loss
        ax = axes[0, 0]
        ax.plot(history['train_loss'], 'b-', linewidth=2)
        ax.set_xlabel('Epoch')
        ax.set_ylabel('Training Loss')
        ax.set_title('Training Loss (Task + Velocity)')
        ax.grid(True, alpha=0.3)
        
        # Solved accuracy
        ax = axes[0, 1]
        ax.plot(epochs_eval[:len(history['solved_T30'])], [s*100 for s in history['solved_T30']], 
               'b-o', label='T=30', linewidth=2)
        ax.plot(epochs_eval[:len(history['solved_T200'])], [s*100 for s in history['solved_T200']], 
               'g-o', label='T=200', linewidth=2)
        ax.set_xlabel('Epoch')
        ax.set_ylabel('Solved Accuracy (%)')
        ax.set_title('Solved Accuracy over Training')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Velocity
        ax = axes[1, 0]
        ax.plot(epochs_eval[:len(history['velocity'])], history['velocity'], 'r-o', linewidth=2)
        ax.set_xlabel('Epoch')
        ax.set_ylabel('Final Velocity @ T=200')
        ax.set_title('Convergence (Lower = More Stable)')
        ax.grid(True, alpha=0.3)
        
        # Comparison bar
        ax = axes[1, 1]
        x = [0, 1]
        vals = [eval_undamped['solved_acc']*100, eval_damped['solved_acc']*100]
        colors = ['red', 'green']
        bars = ax.bar(x, vals, color=colors)
        ax.set_xticks(x)
        ax.set_xticklabels(['Undamped (alpha=1)', f'Damped (alpha={args.damping_alpha})'])
        ax.set_ylabel('Solved @ T=200 (%)')
        ax.set_title('Effect of Damping on Final Accuracy')
        ax.set_ylim(0, max(100, max(vals) + 10))
        for bar, val in zip(bars, vals):
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 1,
                   f'{val:.1f}%', ha='center', va='bottom', fontsize=12, fontweight='bold')
        ax.grid(True, alpha=0.3, axis='y')
        
        plt.tight_layout()
        plt.savefig('logs/sgc_damped_training.png', dpi=150)
        print(f"\nPlot saved to logs/sgc_damped_training.png")
        plt.close()


if __name__ == '__main__':
    main()
