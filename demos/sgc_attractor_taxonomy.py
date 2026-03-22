#!/usr/bin/env python3
"""
SGC Attractor Taxonomy Analysis

This script implements the principled SGC experiment:
1. Stabilize dynamics to T=200 (no NaN)
2. Classify outcomes into:
   - Closed & Correct: Low defect D, violations V=0
   - Closed & Wrong: Low defect D, violations V>0  (Hallucinations)
   - Open/Chaotic: High defect D

3. Measure discriminators between Closed&Correct vs Closed&Wrong:
   - Entropy (sharpness of predictions)
   - Inter-constraint disagreement
   - Convergence velocity ||z_{t+1} - z_t||

This answers the SGC question: What additional macro variables separate
"closed & correct" from "closed & wrong"?

Author: SGC Project
"""

import argparse
import numpy as np
import torch
import torch.nn.functional as F
from pathlib import Path
from collections import defaultdict
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.iterative_spectral_refinement import (
    ISRSolver, SudokuDataset, CoarseProjector
)

try:
    import matplotlib.pyplot as plt
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


def compute_per_puzzle_metrics(model, puzzles, solutions, T=200):
    """Compute per-puzzle metrics for taxonomy classification.
    
    Returns dict with per-puzzle arrays:
    - defect: Commutator defect at final step
    - violations: Total constraint violations
    - entropy: Mean entropy of predictions (sharpness)
    - velocity: ||z_T - z_{T-1}|| (convergence indicator)
    - is_solved: Exact match to ground truth
    - icd: Inter-constraint disagreement
    """
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    B = puzzles.shape[0]
    
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzles)
        z_t = model.z_init.unsqueeze(0).unsqueeze(0).expand(B, 81, -1).clone()
        z_prev = z_t.clone()
        
        # Track trajectory
        defect_traj = []
        velocity_traj = []
        
        for t in range(T):
            # Compute commutator defect
            z_pi = model.Pi(z_t)
            z_combined = z_pi + x_enc
            for block in model.blocks:
                z_combined = block(z_combined)
            z_prime = z_combined
            z_prime_pi = model.Pi(z_prime)
            
            y_prime = F.softmax(model.to_logits(z_prime), dim=-1)
            y_prime_pi = F.softmax(model.to_logits(z_prime_pi), dim=-1)
            kl_per_cell = (y_prime * (y_prime.log() - y_prime_pi.log().clamp(min=-100))).sum(dim=-1)
            defect_per_puzzle = kl_per_cell.mean(dim=-1)  # (B,)
            defect_traj.append(defect_per_puzzle)
            
            # Compute velocity
            velocity = (z_t - z_prev).norm(dim=-1).mean(dim=-1)  # (B,)
            velocity_traj.append(velocity)
            
            # Forward step
            z_prev = z_t.clone()
            y_t, z_t = model.forward_step(z_t, x_enc)
        
        # Final predictions
        y_final = model.to_logits(z_t + x_enc)
        probs = F.softmax(y_final, dim=-1)
        
        # Predictions
        pred = y_final.argmax(dim=-1) + 1
        pred = torch.where(puzzles > 0, puzzles, pred)
        
        # Per-puzzle metrics
        is_solved = (pred == solutions).all(dim=-1).cpu().numpy()  # (B,)
        
        # Violations per puzzle
        pred_grid = pred.view(B, 9, 9)
        row_viols = torch.zeros(B, device=device)
        col_viols = torch.zeros(B, device=device)
        box_viols = torch.zeros(B, device=device)
        
        for i in range(9):
            row = pred_grid[:, i, :]
            col = pred_grid[:, :, i]
            row_viols += 9 - row.unique(dim=1, return_counts=False).shape[1] if B == 1 else (9 - torch.tensor([r.unique().shape[0] for r in row])).float().to(device)
            col_viols += 9 - col.unique(dim=1, return_counts=False).shape[1] if B == 1 else (9 - torch.tensor([c.unique().shape[0] for c in col])).float().to(device)
        
        # Simpler violation count using the model's method
        violations_dict = model.count_constraint_violations(pred)
        total_violations = violations_dict['total_violations']
        
        # Entropy per puzzle (mean over cells)
        entropy = -(probs * probs.log().clamp(min=-100)).sum(dim=-1).mean(dim=-1)  # (B,)
        
        # Inter-constraint disagreement (ICD)
        # Compute row, col, box predictions separately and measure divergence
        z_grid = z_t.view(B, 9, 9, -1)
        y_grid = y_final.view(B, 9, 9, 9)  # (B, row, col, digit)
        
        # Row marginals: mean prediction per row
        row_marg = F.softmax(y_grid.mean(dim=2), dim=-1)  # (B, 9, 9)
        # Col marginals: mean prediction per col
        col_marg = F.softmax(y_grid.mean(dim=1), dim=-1)  # (B, 9, 9)
        # Box marginals
        y_boxes = y_grid.view(B, 3, 3, 3, 3, 9)
        box_marg = F.softmax(y_boxes.mean(dim=(2, 4)), dim=-1).view(B, 9, 9)  # (B, 9, 9)
        
        # ICD: average KL between marginals
        def kl_div(p, q):
            return (p * (p.log() - q.log().clamp(min=-100))).sum(dim=-1)
        
        icd_row_col = kl_div(row_marg, col_marg).mean(dim=-1)
        icd_col_box = kl_div(col_marg, box_marg).mean(dim=-1)
        icd_row_box = kl_div(row_marg, box_marg).mean(dim=-1)
        icd = (icd_row_col + icd_col_box + icd_row_box) / 3  # (B,)
        
        # Stack trajectories
        defect_traj = torch.stack(defect_traj, dim=0)  # (T, B)
        velocity_traj = torch.stack(velocity_traj, dim=0)  # (T, B)
        
        # Final metrics
        final_defect = defect_traj[-1].cpu().numpy()
        final_velocity = velocity_traj[-1].cpu().numpy()
        mean_defect = defect_traj.mean(dim=0).cpu().numpy()
        
        # Check for NaN/explosion
        has_nan = torch.isnan(z_t).any(dim=(1, 2)).cpu().numpy()
        
    return {
        'defect': final_defect,
        'mean_defect': mean_defect,
        'violations': total_violations,
        'entropy': entropy.cpu().numpy(),
        'velocity': final_velocity,
        'is_solved': is_solved,
        'icd': icd.cpu().numpy(),
        'has_nan': has_nan,
        'defect_traj': defect_traj.cpu().numpy(),
        'velocity_traj': velocity_traj.cpu().numpy(),
    }


def classify_outcomes(metrics, defect_threshold=0.02):
    """Classify puzzles into taxonomy categories.
    
    Categories:
    - closed_correct: Low defect, solved (V=0, exact match)
    - closed_wrong: Low defect, not solved (hallucinations)
    - open: High defect
    - diverged: Has NaN
    """
    n = len(metrics['defect'])
    categories = []
    
    for i in range(n):
        if metrics['has_nan'][i]:
            categories.append('diverged')
        elif metrics['defect'][i] > defect_threshold:
            categories.append('open')
        elif metrics['is_solved'][i]:
            categories.append('closed_correct')
        else:
            categories.append('closed_wrong')
    
    return np.array(categories)


def main():
    parser = argparse.ArgumentParser(description="SGC Attractor Taxonomy Analysis")
    parser.add_argument('--num_puzzles', type=int, default=500)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--T', type=int, default=200, help='Number of inference steps')
    parser.add_argument('--train_epochs', type=int, default=50)
    parser.add_argument('--defect_threshold', type=float, default=0.02)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[SGC Taxonomy] Device: {device}")
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate puzzles
    print(f"\n[1/4] Generating {args.num_puzzles} puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    # Train model
    print(f"\n[2/4] Training stabilized model for {args.train_epochs} epochs...")
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
    
    # Run taxonomy analysis
    print(f"\n[3/4] Running T={args.T} inference for taxonomy...")
    test_puzzles = puzzles[:300]
    test_solutions = solutions[:300]
    
    metrics = compute_per_puzzle_metrics(model, test_puzzles, test_solutions, T=args.T)
    
    # Check stability
    print(f"\n  Stability check:")
    print(f"    NaN count: {metrics['has_nan'].sum()} / {len(metrics['has_nan'])}")
    print(f"    Max defect: {np.nanmax(metrics['defect']):.4f}")
    print(f"    Mean velocity at T={args.T}: {np.nanmean(metrics['velocity']):.6f}")
    
    # Classify
    categories = classify_outcomes(metrics, args.defect_threshold)
    
    # Taxonomy counts
    print(f"\n[4/4] ATTRACTOR TAXONOMY RESULTS")
    print("="*60)
    
    cat_counts = {c: (categories == c).sum() for c in ['closed_correct', 'closed_wrong', 'open', 'diverged']}
    for cat, count in cat_counts.items():
        pct = 100 * count / len(categories)
        print(f"  {cat:20s}: {count:4d} ({pct:5.1f}%)")
    
    # Per-category statistics
    print("\n" + "="*60)
    print("PER-CATEGORY METRICS (mean +/- std)")
    print("="*60)
    print(f"{'Category':<20} {'Defect':>10} {'Entropy':>10} {'ICD':>10} {'Velocity':>10}")
    print("-"*60)
    
    for cat in ['closed_correct', 'closed_wrong', 'open']:
        mask = categories == cat
        if mask.sum() == 0:
            continue
        
        d = metrics['defect'][mask]
        e = metrics['entropy'][mask]
        icd = metrics['icd'][mask]
        v = metrics['velocity'][mask]
        
        print(f"{cat:<20} {np.mean(d):>10.4f} {np.mean(e):>10.4f} {np.mean(icd):>10.4f} {np.mean(v):>10.6f}")
    
    # Key discriminator analysis
    print("\n" + "="*60)
    print("DISCRIMINATOR ANALYSIS: Closed&Correct vs Closed&Wrong")
    print("="*60)
    
    cc_mask = categories == 'closed_correct'
    cw_mask = categories == 'closed_wrong'
    
    if cc_mask.sum() > 0 and cw_mask.sum() > 0:
        for metric_name in ['defect', 'entropy', 'icd', 'velocity']:
            cc_vals = metrics[metric_name][cc_mask]
            cw_vals = metrics[metric_name][cw_mask]
            
            # Effect size (Cohen's d)
            pooled_std = np.sqrt((cc_vals.std()**2 + cw_vals.std()**2) / 2)
            effect_size = (cw_vals.mean() - cc_vals.mean()) / (pooled_std + 1e-8)
            
            print(f"\n{metric_name.upper()}:")
            print(f"  Closed&Correct: {np.mean(cc_vals):.4f} +/- {np.std(cc_vals):.4f}")
            print(f"  Closed&Wrong:   {np.mean(cw_vals):.4f} +/- {np.std(cw_vals):.4f}")
            print(f"  Effect size (d): {effect_size:.2f} {'(STRONG)' if abs(effect_size) > 0.8 else '(weak)'}")
    else:
        print("  Not enough samples in both categories for comparison.")
    
    # SGC Conclusion
    print("\n" + "="*60)
    print("SGC CONCLUSION")
    print("="*60)
    
    if cat_counts['diverged'] == 0:
        print("  [OK] Dynamics are STABLE (no NaN at T={})".format(args.T))
    else:
        print("  [WARN] {} puzzles DIVERGED".format(cat_counts['diverged']))
    
    if cat_counts['closed_wrong'] > cat_counts['closed_correct']:
        print("  [INFO] 'Closed & Wrong' dominates -> Need to refine partition Pi")
        print("         or add horizontal energy term for basin selection")
    elif cat_counts['closed_correct'] > cat_counts['closed_wrong']:
        print("  [OK] 'Closed & Correct' dominates -> SGC closure correlates with truth")
    
    # Plot if available
    if MATPLOTLIB_AVAILABLE and cc_mask.sum() > 0 and cw_mask.sum() > 0:
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        
        # Defect vs Entropy scatter
        ax = axes[0, 0]
        ax.scatter(metrics['defect'][cc_mask], metrics['entropy'][cc_mask], 
                  c='green', alpha=0.6, label='Closed & Correct', s=30)
        ax.scatter(metrics['defect'][cw_mask], metrics['entropy'][cw_mask], 
                  c='red', alpha=0.6, label='Closed & Wrong', s=30)
        ax.axvline(args.defect_threshold, color='gray', linestyle='--', label=f'Defect threshold={args.defect_threshold}')
        ax.set_xlabel('Commutator Defect')
        ax.set_ylabel('Entropy')
        ax.set_title('Defect vs Entropy')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # ICD comparison
        ax = axes[0, 1]
        ax.hist(metrics['icd'][cc_mask], bins=20, alpha=0.6, color='green', label='Closed & Correct', density=True)
        ax.hist(metrics['icd'][cw_mask], bins=20, alpha=0.6, color='red', label='Closed & Wrong', density=True)
        ax.set_xlabel('Inter-Constraint Disagreement (ICD)')
        ax.set_ylabel('Density')
        ax.set_title('ICD Distribution')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Velocity comparison
        ax = axes[1, 0]
        ax.hist(metrics['velocity'][cc_mask], bins=20, alpha=0.6, color='green', label='Closed & Correct', density=True)
        ax.hist(metrics['velocity'][cw_mask], bins=20, alpha=0.6, color='red', label='Closed & Wrong', density=True)
        ax.set_xlabel('Final Velocity ||z_T - z_{T-1}||')
        ax.set_ylabel('Density')
        ax.set_title('Convergence Velocity')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Defect trajectory (mean per category)
        ax = axes[1, 1]
        T_plot = min(100, args.T)  # Plot first 100 steps
        defect_traj = metrics['defect_traj'][:T_plot]
        ax.plot(np.nanmean(defect_traj[:, cc_mask], axis=1), 'g-', label='Closed & Correct', linewidth=2)
        ax.plot(np.nanmean(defect_traj[:, cw_mask], axis=1), 'r-', label='Closed & Wrong', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Mean Commutator Defect')
        ax.set_title('Defect Trajectory by Category')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('logs/sgc_attractor_taxonomy.png', dpi=150)
        print(f"\nPlot saved to logs/sgc_attractor_taxonomy.png")
        plt.close()


if __name__ == '__main__':
    main()
