#!/usr/bin/env python3
"""
SGC Defect-Halting Evaluation

This script validates the core SGC hypothesis:
    "Closure → Truth": Low commutator defect predicts correct solutions.

The test:
1. Load a trained model (or train a fresh one)
2. Run defect-halting inference at various epsilon thresholds
3. Plot: Solved_Accuracy vs Defect_Threshold

If SGC is correct:
- Solved accuracy should increase as defect threshold decreases
- Low defect should be a high-precision predictor of "solved"

Author: SGC Project
"""

import argparse
import numpy as np
import torch
import torch.nn.functional as F
from pathlib import Path
import sys

# Add parent to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.iterative_spectral_refinement import (
    ISRSolver, SudokuDataset, CoarseProjector
)

try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


def evaluate_defect_halting(model, puzzles, solutions, eps_values, max_steps=100):
    """Evaluate model with defect-halting at various epsilon thresholds.
    
    Returns dict mapping eps -> {solved_acc, cell_acc, avg_steps, converged_ratio}
    """
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    results = {}
    
    with torch.no_grad():
        for eps in eps_values:
            print(f"  eps={eps:.4f}...", end=" ", flush=True)
            
            # Run defect-halting inference
            out = model.forward_defect_halting(puzzles, max_steps=max_steps, eps=eps)
            
            # Compute accuracy
            acc = model.compute_accuracy(out['y_final'], solutions, puzzles)
            
            results[eps] = {
                'solved_acc': acc['solved_acc'],
                'cell_acc': acc['cell_acc'],
                'avg_steps': out['steps_taken'],
                'final_defect': out['final_defect'],
                'converged': out['converged'],
            }
            
            print(f"solved={acc['solved_acc']*100:.1f}%, steps={out['steps_taken']:.1f}")
    
    return results


def evaluate_fixed_steps(model, puzzles, solutions, step_values):
    """Evaluate model with fixed number of steps (baseline comparison).
    
    Returns dict mapping T -> {solved_acc, cell_acc, final_defect}
    """
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    results = {}
    
    with torch.no_grad():
        for T in step_values:
            print(f"  T={T}...", end=" ", flush=True)
            
            # Run with commutator defect tracking
            out = model.forward_with_commutator_defect(puzzles, T=T)
            
            # Compute accuracy
            acc = model.compute_accuracy(out['y_final'], solutions, puzzles)
            
            # Final defect
            final_defect = out['defect_traj'][-1].item() if len(out['defect_traj']) > 0 else float('inf')
            
            results[T] = {
                'solved_acc': acc['solved_acc'],
                'cell_acc': acc['cell_acc'],
                'final_defect': final_defect,
            }
            
            print(f"solved={acc['solved_acc']*100:.1f}%, defect={final_defect:.4f}")
    
    return results


def analyze_defect_vs_correctness(model, puzzles, solutions, T=30):
    """Per-puzzle analysis: Is low defect a predictor of correctness?
    
    Returns arrays for scatter plot and precision/recall analysis.
    """
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    
    with torch.no_grad():
        out = model.forward_with_commutator_defect(puzzles, T=T)
        
        # Per-puzzle correctness
        pred = out['y_final'].argmax(dim=-1) + 1
        pred = torch.where(puzzles > 0, puzzles, pred)
        is_solved = (pred == solutions).all(dim=-1).cpu().numpy()  # (B,)
        
        # Per-puzzle final defect (batch-level for now, would need per-sample)
        final_defect = out['defect_traj'][-1].item()
        
        # Compute per-puzzle defect by running forward step on each
        x_enc = model.encode_puzzle(puzzles)
        z_t = model.z_init.unsqueeze(0).unsqueeze(0).expand(puzzles.shape[0], 81, -1).clone()
        
        for _ in range(T):
            _, z_t = model.forward_step(z_t, x_enc)
        
        # Compute commutator defect per sample
        z_pi = model.Pi(z_t)
        z_combined = z_pi + x_enc
        for block in model.blocks:
            z_combined = block(z_combined)
        z_prime = z_combined
        z_prime_pi = model.Pi(z_prime)
        
        y_prime = F.softmax(model.to_logits(z_prime), dim=-1)
        y_prime_pi = F.softmax(model.to_logits(z_prime_pi), dim=-1)
        kl_per_cell = (y_prime * (y_prime.log() - y_prime_pi.log().clamp(min=-100))).sum(dim=-1)
        defect_per_puzzle = kl_per_cell.mean(dim=-1).cpu().numpy()  # (B,)
    
    return defect_per_puzzle, is_solved


def main():
    parser = argparse.ArgumentParser(description="SGC Defect-Halting Evaluation")
    parser.add_argument('--num_puzzles', type=int, default=500, help='Number of test puzzles')
    parser.add_argument('--hidden_dim', type=int, default=32, help='Model hidden dimension')
    parser.add_argument('--num_blocks', type=int, default=2, help='Number of Fisher-Axial blocks')
    parser.add_argument('--max_steps', type=int, default=100, help='Max steps for defect-halting')
    parser.add_argument('--train_epochs', type=int, default=20, help='Quick training epochs')
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[SGC Eval] Device: {device}")
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate test puzzles
    print(f"\n[1/4] Generating {args.num_puzzles} test puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    # Create and quick-train model
    print(f"\n[2/4] Training model for {args.train_epochs} epochs...")
    model = ISRSolver(args.hidden_dim, args.num_blocks).to(device)
    
    # Quick training
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
        
        if (epoch + 1) % 5 == 0:
            # Quick eval
            model.eval()
            with torch.no_grad():
                test_batch = puzzles[:100].to(device)
                test_sol = solutions[:100].to(device)
                out = model(test_batch, T=30)
                acc = model.compute_accuracy(out['y_final'], test_sol, test_batch)
            print(f"  Epoch {epoch+1}: loss={total_loss/n_batches:.4f}, "
                  f"cell={acc['cell_acc']*100:.1f}%, solved={acc['solved_acc']*100:.1f}%")
    
    # Evaluate with fixed steps (baseline)
    print(f"\n[3/4] Evaluating with fixed steps...")
    step_values = [5, 10, 20, 30, 50, 75, 100]
    fixed_results = evaluate_fixed_steps(model, puzzles[:200], solutions[:200], step_values)
    
    # Evaluate with defect-halting
    print(f"\n[4/4] Evaluating with defect-halting...")
    eps_values = [1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.001]
    defect_results = evaluate_defect_halting(
        model, puzzles[:200], solutions[:200], eps_values, max_steps=args.max_steps
    )
    
    # Analyze defect vs correctness
    print("\n[Analysis] Defect vs Correctness correlation...")
    defects, is_solved = analyze_defect_vs_correctness(model, puzzles[:200], solutions[:200], T=30)
    
    solved_defects = defects[is_solved]
    unsolved_defects = defects[~is_solved]
    
    print(f"  Solved puzzles ({is_solved.sum()}): mean defect = {solved_defects.mean():.4f}")
    print(f"  Unsolved puzzles ({(~is_solved).sum()}): mean defect = {unsolved_defects.mean():.4f}")
    
    # Summary
    print("\n" + "="*60)
    print("SGC VALIDATION SUMMARY")
    print("="*60)
    
    print("\nFixed Steps (baseline):")
    print(f"{'Steps':>8} {'Solved%':>10} {'Cell%':>10} {'Defect':>10}")
    for T, r in sorted(fixed_results.items()):
        print(f"{T:>8} {r['solved_acc']*100:>10.1f} {r['cell_acc']*100:>10.1f} {r['final_defect']:>10.4f}")
    
    print("\nDefect-Halting:")
    print(f"{'Epsilon':>10} {'Solved%':>10} {'Steps':>10} {'Final D':>10}")
    for eps, r in sorted(defect_results.items(), reverse=True):
        print(f"{eps:>10.4f} {r['solved_acc']*100:>10.1f} {r['avg_steps']:>10.1f} {r['final_defect']:>10.4f}")
    
    print("\n" + "="*60)
    print("SGC HYPOTHESIS TEST:")
    print("  If 'Closure -> Truth', then:")
    print("    1. Solved accuracy should increase with tighter epsilon")
    print("    2. Low defect should predict solved puzzles")
    print("="*60)
    
    # Plot if matplotlib available
    if MATPLOTLIB_AVAILABLE:
        fig, axes = plt.subplots(1, 3, figsize=(15, 4))
        
        # Plot 1: Fixed steps - solved acc vs steps
        ax1 = axes[0]
        steps = sorted(fixed_results.keys())
        solved_accs = [fixed_results[s]['solved_acc']*100 for s in steps]
        ax1.plot(steps, solved_accs, 'b-o', linewidth=2, markersize=8)
        ax1.set_xlabel('Number of Steps')
        ax1.set_ylabel('Solved Accuracy (%)')
        ax1.set_title('Fixed Steps: Accuracy vs Compute')
        ax1.grid(True, alpha=0.3)
        
        # Plot 2: Defect-halting - solved acc vs epsilon
        ax2 = axes[1]
        epsilons = sorted(defect_results.keys(), reverse=True)
        solved_accs = [defect_results[e]['solved_acc']*100 for e in epsilons]
        ax2.semilogx(epsilons, solved_accs, 'r-o', linewidth=2, markersize=8)
        ax2.set_xlabel('Defect Threshold (epsilon)')
        ax2.set_ylabel('Solved Accuracy (%)')
        ax2.set_title('Defect-Halting: Accuracy vs Threshold')
        ax2.invert_xaxis()  # Lower epsilon = tighter = on right
        ax2.grid(True, alpha=0.3)
        
        # Plot 3: Scatter - defect vs correctness
        ax3 = axes[2]
        ax3.scatter(defects[~is_solved], np.zeros(sum(~is_solved)), 
                   c='red', alpha=0.5, label='Unsolved', s=50)
        ax3.scatter(defects[is_solved], np.ones(sum(is_solved)), 
                   c='green', alpha=0.5, label='Solved', s=50)
        ax3.set_xlabel('Commutator Defect')
        ax3.set_ylabel('Solved (1) / Unsolved (0)')
        ax3.set_title('SGC Test: Defect vs Correctness')
        ax3.legend()
        ax3.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('logs/sgc_defect_halting_eval.png', dpi=150)
        print(f"\nPlot saved to logs/sgc_defect_halting_eval.png")
        plt.close()


if __name__ == '__main__':
    main()
