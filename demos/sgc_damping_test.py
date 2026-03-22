#!/usr/bin/env python3
"""
SGC Krasnosel'skii-Mann Damping Test

Diagnostic test: Can we fix overshoot with inference-only damping?

The damped iteration:
    z_{t+1} = (1 - alpha) * z_t + alpha * F(z_t)

This turns non-expansive operators into convergent iterations by averaging
out oscillations. If the correct solution IS a fixed point but dynamically
unstable, damping will lock it in.

Outcomes:
1) Solved@200 jumps, residual -> 0: Overshoot fixed, bake damping into model
2) Residual collapses but still wrong: Basin selection problem, need energy term
3) Residual stays high: Not averaged operator, need Jacobian regularization

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

try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


def run_damped_inference(model, puzzles, solutions, T=200, alpha=0.5):
    """Run inference with Krasnosel'skii-Mann damping.
    
    z_{t+1} = (1 - alpha) * z_t + alpha * F(z_t)
    
    Returns per-step metrics for analysis.
    """
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    B = puzzles.shape[0]
    
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzles)
        z_t = model.z_init.unsqueeze(0).unsqueeze(0).expand(B, 81, -1).clone()
        
        # Track metrics over time
        residual_traj = []  # ||z_{t+1} - z_t||
        solved_traj = []    # Solved accuracy at each step
        defect_traj = []    # Commutator defect
        
        for t in range(T):
            # Compute F(z_t) - the raw update
            y_t, z_next_raw = model.forward_step(z_t, x_enc)
            
            # DAMPED UPDATE: z_{t+1} = (1-alpha)*z_t + alpha*F(z_t)
            z_next = (1 - alpha) * z_t + alpha * z_next_raw
            
            # Residual (velocity)
            residual = (z_next - z_t).norm(dim=-1).mean(dim=-1)  # (B,)
            residual_traj.append(residual.mean().item())
            
            # Solved accuracy at this step
            y_current = model.to_logits(z_next + x_enc)
            pred = y_current.argmax(dim=-1) + 1
            pred = torch.where(puzzles > 0, puzzles, pred)
            is_solved = (pred == solutions).all(dim=-1).float().mean().item()
            solved_traj.append(is_solved)
            
            # Commutator defect
            z_pi = model.Pi(z_next)
            z_combined = z_pi + x_enc
            for block in model.blocks:
                z_combined = block(z_combined)
            z_prime = z_combined
            z_prime_pi = model.Pi(z_prime)
            
            y_prime = F.softmax(model.to_logits(z_prime), dim=-1)
            y_prime_pi = F.softmax(model.to_logits(z_prime_pi), dim=-1)
            kl = (y_prime * (y_prime.log() - y_prime_pi.log().clamp(min=-100))).sum(dim=-1)
            defect_traj.append(kl.mean().item())
            
            z_t = z_next
        
        # Final metrics
        y_final = model.to_logits(z_t + x_enc)
        pred_final = y_final.argmax(dim=-1) + 1
        pred_final = torch.where(puzzles > 0, puzzles, pred_final)
        
        is_solved_final = (pred_final == solutions).all(dim=-1)
        solved_final = is_solved_final.float().mean().item()
        
        # Violations
        violations = model.count_constraint_violations(pred_final)
        
    return {
        'residual_traj': residual_traj,
        'solved_traj': solved_traj,
        'defect_traj': defect_traj,
        'solved_final': solved_final,
        'residual_final': residual_traj[-1],
        'defect_final': defect_traj[-1],
        'violations': violations['total_violations'],
    }


def main():
    parser = argparse.ArgumentParser(description="SGC KM Damping Test")
    parser.add_argument('--num_puzzles', type=int, default=400)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--T', type=int, default=200)
    parser.add_argument('--train_epochs', type=int, default=50)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[KM Damping Test] Device: {device}")
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate puzzles
    print(f"\n[1/4] Generating {args.num_puzzles} puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    # Train model (same as before)
    print(f"\n[2/4] Training model for {args.train_epochs} epochs...")
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
                test_batch = puzzles[:100].to(device)
                test_sol = solutions[:100].to(device)
                out = model(test_batch, T=30)
                acc = model.compute_accuracy(out['y_final'], test_sol, test_batch)
            print(f"  Epoch {epoch+1}: loss={total_loss/n_batches:.4f}, "
                  f"cell={acc['cell_acc']*100:.1f}%, solved={acc['solved_acc']*100:.1f}%")
    
    # Baseline: No damping (alpha=1.0)
    print(f"\n[3/4] Running damping sweep at T={args.T}...")
    test_puzzles = puzzles[:200]
    test_solutions = solutions[:200]
    
    alpha_values = [1.0, 0.8, 0.5, 0.25, 0.1]
    results = {}
    
    for alpha in alpha_values:
        print(f"\n  Alpha = {alpha}...")
        r = run_damped_inference(model, test_puzzles, test_solutions, T=args.T, alpha=alpha)
        results[alpha] = r
        print(f"    Solved@{args.T}: {r['solved_final']*100:.1f}%")
        print(f"    Residual@{args.T}: {r['residual_final']:.6f}")
        print(f"    Defect@{args.T}: {r['defect_final']:.4f}")
        print(f"    Violations: {r['violations']:.1f}")
    
    # Summary
    print("\n" + "="*70)
    print("KRASNOSEL'SKII-MANN DAMPING TEST RESULTS")
    print("="*70)
    print(f"{'Alpha':>8} {'Solved%':>10} {'Residual':>12} {'Defect':>10} {'Violations':>12}")
    print("-"*70)
    
    for alpha in alpha_values:
        r = results[alpha]
        print(f"{alpha:>8.2f} {r['solved_final']*100:>10.1f} {r['residual_final']:>12.6f} "
              f"{r['defect_final']:>10.4f} {r['violations']:>12.1f}")
    
    # Diagnosis
    print("\n" + "="*70)
    print("DIAGNOSIS")
    print("="*70)
    
    baseline = results[1.0]
    best_alpha = max([a for a in alpha_values if a < 1.0], 
                     key=lambda a: results[a]['solved_final'])
    best = results[best_alpha]
    
    solved_improvement = best['solved_final'] - baseline['solved_final']
    residual_reduction = baseline['residual_final'] - best['residual_final']
    
    if solved_improvement > 0.1:  # >10% improvement
        print(f"[OUTCOME 1] OVERSHOOT FIXED!")
        print(f"  Best alpha: {best_alpha}")
        print(f"  Solved improvement: {baseline['solved_final']*100:.1f}% -> {best['solved_final']*100:.1f}%")
        print(f"  Residual reduction: {baseline['residual_final']:.4f} -> {best['residual_final']:.4f}")
        print(f"\n  NEXT: Bake damping into model (learned alpha or fixed)")
    elif best['residual_final'] < 0.01 and best['solved_final'] < 0.1:
        print(f"[OUTCOME 2] RESIDUAL COLLAPSED BUT STILL WRONG")
        print(f"  Best alpha: {best_alpha}")
        print(f"  Residual: {best['residual_final']:.6f} (converged)")
        print(f"  Solved: {best['solved_final']*100:.1f}% (still low)")
        print(f"\n  DIAGNOSIS: Basin selection problem. Correct solution is NOT an attractor.")
        print(f"  NEXT: Add task-alignment term to make correct solutions fixed points")
    elif best['residual_final'] > 0.1:
        print(f"[OUTCOME 3] RESIDUAL STAYS HIGH")
        print(f"  Best residual: {best['residual_final']:.4f}")
        print(f"\n  DIAGNOSIS: Operator not averaged/nonexpansive. Limit cycle or chaos.")
        print(f"  NEXT: Jacobian spectral radius regularization")
    else:
        print(f"[MIXED OUTCOME]")
        print(f"  Some improvement but inconclusive.")
        print(f"  Solved: {baseline['solved_final']*100:.1f}% -> {best['solved_final']*100:.1f}%")
        print(f"  Residual: {baseline['residual_final']:.4f} -> {best['residual_final']:.4f}")
    
    # Plot
    if MATPLOTLIB_AVAILABLE:
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        
        # Residual trajectory
        ax = axes[0, 0]
        for alpha in [1.0, 0.5, 0.25, 0.1]:
            r = results[alpha]
            ax.semilogy(r['residual_traj'], label=f'alpha={alpha}', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Residual ||z_{t+1} - z_t||')
        ax.set_title('Residual Trajectory (log scale)')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Solved trajectory
        ax = axes[0, 1]
        for alpha in [1.0, 0.5, 0.25, 0.1]:
            r = results[alpha]
            ax.plot([s*100 for s in r['solved_traj']], label=f'alpha={alpha}', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Solved Accuracy (%)')
        ax.set_title('Solved Accuracy over Time')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Defect trajectory
        ax = axes[1, 0]
        for alpha in [1.0, 0.5, 0.25, 0.1]:
            r = results[alpha]
            ax.plot(r['defect_traj'], label=f'alpha={alpha}', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Commutator Defect')
        ax.set_title('Defect Trajectory')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Summary bar chart
        ax = axes[1, 1]
        alphas = [1.0, 0.8, 0.5, 0.25, 0.1]
        solved_vals = [results[a]['solved_final']*100 for a in alphas]
        x = np.arange(len(alphas))
        bars = ax.bar(x, solved_vals, color=['red' if a==1.0 else 'green' for a in alphas])
        ax.set_xticks(x)
        ax.set_xticklabels([f'{a}' for a in alphas])
        ax.set_xlabel('Damping Alpha')
        ax.set_ylabel('Solved Accuracy @ T=200 (%)')
        ax.set_title('Effect of KM Damping on Solved Accuracy')
        ax.grid(True, alpha=0.3, axis='y')
        
        # Add value labels on bars
        for bar, val in zip(bars, solved_vals):
            ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 1,
                   f'{val:.1f}%', ha='center', va='bottom', fontsize=10)
        
        plt.tight_layout()
        plt.savefig('logs/sgc_damping_test.png', dpi=150)
        print(f"\nPlot saved to logs/sgc_damping_test.png")
        plt.close()


if __name__ == '__main__':
    main()
