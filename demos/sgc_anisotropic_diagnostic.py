#!/usr/bin/env python3
"""
SGC Anisotropic Velocity Diagnostic

Plot r_parallel = ||Π Δz|| vs r_perp = ||(I-Π) Δz|| over time.

If r_parallel >> r_perp: Horizontal sliding (overshoot along manifold)
If r_perp >> r_parallel: Vertical leakage (leaving coarse subspace)

This diagnostic confirms whether λ_parallel > λ_perp is the right dissipation.

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


def run_anisotropic_diagnostic(model, puzzles, solutions, T=200, alpha=1.0):
    """Measure horizontal (Π Δz) vs vertical ((I-Π) Δz) velocity components."""
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    B = puzzles.shape[0]
    
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzles)
        z_t = model.z_init.unsqueeze(0).unsqueeze(0).expand(B, 81, -1).clone()
        
        r_parallel_traj = []  # ||Π Δz||
        r_perp_traj = []      # ||(I-Π) Δz||
        r_total_traj = []     # ||Δz||
        solved_traj = []
        
        for t in range(T):
            z_prev = z_t
            
            # Forward step
            y_t, z_next_raw = model.forward_step(z_t, x_enc)
            
            # Apply damping if alpha < 1
            if alpha < 1.0:
                z_next = (1 - alpha) * z_prev + alpha * z_next_raw
            else:
                z_next = z_next_raw
            
            # Compute Δz
            delta_z = z_next - z_prev  # (B, 81, D)
            
            # Project onto coarse subspace: Π Δz (horizontal component)
            pi_delta_z = model.Pi(delta_z)
            
            # Orthogonal complement: (I - Π) Δz (vertical component)
            perp_delta_z = delta_z - pi_delta_z
            
            # Compute norms (mean over batch and cells)
            r_parallel = pi_delta_z.norm(dim=-1).mean().item()
            r_perp = perp_delta_z.norm(dim=-1).mean().item()
            r_total = delta_z.norm(dim=-1).mean().item()
            
            r_parallel_traj.append(r_parallel)
            r_perp_traj.append(r_perp)
            r_total_traj.append(r_total)
            
            # Solved accuracy
            y_current = model.to_logits(z_next + x_enc)
            pred = y_current.argmax(dim=-1) + 1
            pred = torch.where(puzzles > 0, puzzles, pred)
            is_solved = (pred == solutions).all(dim=-1).float().mean().item()
            solved_traj.append(is_solved)
            
            z_t = z_next
    
    return {
        'r_parallel': np.array(r_parallel_traj),
        'r_perp': np.array(r_perp_traj),
        'r_total': np.array(r_total_traj),
        'solved': np.array(solved_traj),
    }


def main():
    parser = argparse.ArgumentParser(description="SGC Anisotropic Velocity Diagnostic")
    parser.add_argument('--num_puzzles', type=int, default=400)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--T', type=int, default=200)
    parser.add_argument('--train_epochs', type=int, default=50)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Anisotropic Diagnostic] Device: {device}")
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate and train
    print(f"\n[1/3] Generating {args.num_puzzles} puzzles...")
    puzzles, solutions, _ = SudokuDataset.generate_puzzles(
        args.num_puzzles, min_clues=45, max_clues=55, require_unique=True
    )
    puzzles = torch.tensor(puzzles, dtype=torch.long)
    solutions = torch.tensor(solutions, dtype=torch.long)
    
    print(f"\n[2/3] Training model for {args.train_epochs} epochs...")
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
    
    # Run diagnostic
    print(f"\n[3/3] Running anisotropic diagnostic at T={args.T}...")
    test_puzzles = puzzles[:200]
    test_solutions = solutions[:200]
    
    results = {}
    for alpha in [1.0, 0.1]:
        print(f"\n  Alpha = {alpha}...")
        r = run_anisotropic_diagnostic(model, test_puzzles, test_solutions, T=args.T, alpha=alpha)
        results[alpha] = r
        
        # Summary stats
        mean_parallel = r['r_parallel'].mean()
        mean_perp = r['r_perp'].mean()
        ratio = mean_parallel / (mean_perp + 1e-8)
        
        print(f"    Mean ||Pi dz|| (horizontal): {mean_parallel:.6f}")
        print(f"    Mean ||(I-Pi) dz|| (vertical): {mean_perp:.6f}")
        print(f"    Ratio (parallel/perp): {ratio:.2f}")
        print(f"    Final solved: {r['solved'][-1]*100:.1f}%")
    
    # Analysis
    print("\n" + "="*70)
    print("ANISOTROPIC DIAGNOSTIC RESULTS")
    print("="*70)
    
    undamped = results[1.0]
    damped = results[0.1]
    
    ratio_undamped = undamped['r_parallel'].mean() / (undamped['r_perp'].mean() + 1e-8)
    ratio_damped = damped['r_parallel'].mean() / (damped['r_perp'].mean() + 1e-8)
    
    print(f"\nAlpha=1.0 (undamped):")
    print(f"  Horizontal/Vertical ratio: {ratio_undamped:.2f}")
    print(f"  Solved@{args.T}: {undamped['solved'][-1]*100:.1f}%")
    
    print(f"\nAlpha=0.1 (damped):")
    print(f"  Horizontal/Vertical ratio: {ratio_damped:.2f}")
    print(f"  Solved@{args.T}: {damped['solved'][-1]*100:.1f}%")
    
    print("\n" + "="*70)
    print("DIAGNOSIS")
    print("="*70)
    
    if ratio_undamped > 2.0:
        print(f"\n[CONFIRMED] Horizontal sliding dominates (ratio={ratio_undamped:.1f}x)")
        print("  -> Use λ_parallel >> λ_perp in anisotropic dissipation")
        print("  -> Recommended: λ_parallel=1.0, λ_perp=0.1")
    elif ratio_undamped < 0.5:
        print(f"\n[SURPRISING] Vertical leakage dominates (ratio={ratio_undamped:.1f}x)")
        print("  -> Use λ_perp >> λ_parallel")
    else:
        print(f"\n[MIXED] Both components comparable (ratio={ratio_undamped:.1f}x)")
        print("  -> Use balanced dissipation")
    
    # Plot
    if MATPLOTLIB_AVAILABLE:
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        
        # Horizontal vs Vertical (undamped)
        ax = axes[0, 0]
        ax.semilogy(undamped['r_parallel'], 'b-', label='||Π Δz|| (horizontal)', linewidth=2)
        ax.semilogy(undamped['r_perp'], 'r-', label='||(I-Π) Δz|| (vertical)', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Velocity component (log)')
        ax.set_title('Alpha=1.0 (Undamped): Horizontal vs Vertical')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Horizontal vs Vertical (damped)
        ax = axes[0, 1]
        ax.semilogy(damped['r_parallel'], 'b-', label='||Π Δz|| (horizontal)', linewidth=2)
        ax.semilogy(damped['r_perp'], 'r-', label='||(I-Π) Δz|| (vertical)', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Velocity component (log)')
        ax.set_title('Alpha=0.1 (Damped): Horizontal vs Vertical')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Ratio over time
        ax = axes[1, 0]
        ratio_undamped_t = undamped['r_parallel'] / (undamped['r_perp'] + 1e-8)
        ratio_damped_t = damped['r_parallel'] / (damped['r_perp'] + 1e-8)
        ax.plot(ratio_undamped_t, 'b-', label='Alpha=1.0', linewidth=2)
        ax.plot(ratio_damped_t, 'g-', label='Alpha=0.1', linewidth=2)
        ax.axhline(1.0, color='gray', linestyle='--', label='Equal')
        ax.set_xlabel('Step t')
        ax.set_ylabel('Horizontal/Vertical Ratio')
        ax.set_title('Anisotropy Ratio Over Time')
        ax.legend()
        ax.grid(True, alpha=0.3)
        ax.set_ylim(0, min(20, max(ratio_undamped_t.max(), ratio_damped_t.max()) * 1.1))
        
        # Solved trajectory
        ax = axes[1, 1]
        ax.plot(undamped['solved'] * 100, 'b-', label='Alpha=1.0', linewidth=2)
        ax.plot(damped['solved'] * 100, 'g-', label='Alpha=0.1', linewidth=2)
        ax.set_xlabel('Step t')
        ax.set_ylabel('Solved Accuracy (%)')
        ax.set_title('Solved Accuracy Over Time')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('logs/sgc_anisotropic_diagnostic.png', dpi=150)
        print(f"\nPlot saved to logs/sgc_anisotropic_diagnostic.png")
        plt.close()


if __name__ == '__main__':
    main()
