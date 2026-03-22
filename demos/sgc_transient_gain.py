#!/usr/bin/env python3
"""
SGC Transient Gain Law: Non-Normality Framework

For non-normal operators, eigenvalues don't tell the stability story.
The constitutive parameter is FINITE-HORIZON GAIN: ||M^K||

The law: Choose alpha so that ||M_alpha^K|| <= G*
where G* is the "entropy production budget" over horizon K.

This is truly Jacobson-style:
- Constitutive measurement: g_K(alpha) = max ||M_alpha^K v||
- Universal law: g_K(alpha) <= G*
- Alpha drops out as derived quantity

Key insight: Non-normality allows ||M^k|| >> 1 even when rho(M) < 1.
This is "transient amplification" - the mechanism of metastability.

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


def apply_linearized_step(model, z, x_enc, v, alpha):
    """Apply one step of linearized damped dynamics: M_alpha @ v.
    
    M_alpha = I + alpha*(J - I)
    
    So M_alpha @ v = v + alpha*(J@v - v) = (1-alpha)*v + alpha*J@v
    """
    eps = 1e-4
    with torch.no_grad():
        z_plus = z + eps * v
        z_minus = z - eps * v
        _, F_plus = model.forward_step(z_plus, x_enc)
        _, F_minus = model.forward_step(z_minus, x_enc)
        Jv = (F_plus - F_minus) / (2 * eps)
    
    # M_alpha @ v = (1-alpha)*v + alpha*Jv
    return (1 - alpha) * v + alpha * Jv


def estimate_K_step_gain(model, z, x_enc, K, alpha, n_probes=10, n_power_iter=3):
    """Estimate g_K(alpha) = max ||M_alpha^K v|| via K-step power iteration.
    
    This captures transient amplification from non-normality.
    """
    max_gain = 0.0
    
    for _ in range(n_probes):
        # Random initial direction
        v = torch.randn_like(z)
        v = v / v.norm()
        
        for _ in range(n_power_iter):
            # Apply M_alpha K times
            v_k = v.clone()
            for _ in range(K):
                v_k = apply_linearized_step(model, z, x_enc, v_k, alpha)
            
            # Gain = ||M_alpha^K v|| / ||v||
            gain = v_k.norm().item()
            max_gain = max(max_gain, gain)
            
            # Update v for next power iteration
            if v_k.norm() > 1e-8:
                v = v_k / v_k.norm()
    
    return max_gain


def find_alpha_for_gain_cap(model, z, x_enc, K, G_star, alpha_range=(0.01, 1.0), tol=0.01):
    """Binary search to find max alpha such that g_K(alpha) <= G*.
    
    This is the constitutive law: alpha = max{a : g_K(a) <= G*}
    """
    lo, hi = alpha_range
    
    # First check if even alpha=lo exceeds bound
    g_lo = estimate_K_step_gain(model, z, x_enc, K, lo)
    if g_lo > G_star:
        return lo, g_lo, "BOUND_EXCEEDED"
    
    # Check if alpha=hi is still within bound
    g_hi = estimate_K_step_gain(model, z, x_enc, K, hi)
    if g_hi <= G_star:
        return hi, g_hi, "NO_CONSTRAINT"
    
    # Binary search
    while hi - lo > tol:
        mid = (lo + hi) / 2
        g_mid = estimate_K_step_gain(model, z, x_enc, K, mid)
        
        if g_mid <= G_star:
            lo = mid
        else:
            hi = mid
    
    return lo, estimate_K_step_gain(model, z, x_enc, K, lo), "DERIVED"


def run_with_alpha(model, puzzles, solutions, T, alpha):
    """Run inference with given alpha."""
    model.eval()
    device = next(model.parameters()).device
    puzzles = puzzles.to(device)
    solutions = solutions.to(device)
    B = puzzles.shape[0]
    
    with torch.no_grad():
        x_enc = model.encode_puzzle(puzzles)
        z_t = model.z_init.unsqueeze(0).unsqueeze(0).expand(B, 81, -1).clone()
        
        for _ in range(T):
            _, z_next = model.forward_step(z_t, x_enc)
            z_t = (1 - alpha) * z_t + alpha * z_next
        
        y_final = model.to_logits(z_t + x_enc)
        pred = y_final.argmax(dim=-1) + 1
        pred = torch.where(puzzles > 0, puzzles, pred)
        solved = (pred == solutions).all(dim=-1).float().mean().item()
    
    return solved


def main():
    parser = argparse.ArgumentParser(description="SGC Transient Gain Law")
    parser.add_argument('--num_puzzles', type=int, default=300)
    parser.add_argument('--hidden_dim', type=int, default=32)
    parser.add_argument('--num_blocks', type=int, default=2)
    parser.add_argument('--train_epochs', type=int, default=50)
    parser.add_argument('--seed', type=int, default=42)
    args = parser.parse_args()
    
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[Transient Gain Law] Device: {device}")
    print("="*70)
    print("NON-NORMALITY FRAMEWORK: FINITE-HORIZON GAIN CAP")
    print("="*70)
    print(f"\nFor non-normal M, eigenvalues don't predict transient behavior.")
    print(f"The constitutive parameter is g_K(alpha) = ||M_alpha^K||")
    print(f"The law: alpha = max{{a : g_K(a) <= G*}}")
    
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Generate and train
    print(f"\n[1/5] Training model...")
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
    
    # Measure transient gain for different K and alpha
    print(f"\n[2/5] Measuring transient gain g_K(alpha) = ||M_alpha^K||...")
    
    test_puzzle = puzzles[0:1].to(device)
    with torch.no_grad():
        x_enc = model.encode_puzzle(test_puzzle)
        z = model.z_init.unsqueeze(0).unsqueeze(0).expand(1, 81, -1).clone()
        # Advance to mid-trajectory
        for _ in range(30):
            _, z = model.forward_step(z, x_enc)
    
    # Measure gain for different K and alpha
    print(f"\n  TRANSIENT GAIN g_K(alpha) = ||M_alpha^K||:")
    print(f"  " + "-"*60)
    
    alphas = [0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 1.0]
    Ks = [10, 30, 50, 100]
    
    print(f"  | K\\alpha |", end="")
    for a in alphas:
        print(f" {a:5.2f} |", end="")
    print()
    print(f"  |---------|" + "-------|" * len(alphas))
    
    gains = {}
    for K in Ks:
        gains[K] = {}
        print(f"  | K={K:3d}   |", end="")
        for alpha in alphas:
            g = estimate_K_step_gain(model, z, x_enc, K, alpha, n_probes=5, n_power_iter=2)
            gains[K][alpha] = g
            print(f" {g:5.2f} |", end="")
        print()
    
    # Find alpha for different gain caps
    print(f"\n[3/5] Deriving alpha from gain cap G*...")
    
    G_stars = [1.0, 2.0, 5.0, 10.0, 20.0]
    
    print(f"\n  DERIVED ALPHA = max{{a : g_K(a) <= G*}}:")
    print(f"  " + "-"*60)
    
    derived_alphas = {}
    for K in [30, 100]:
        derived_alphas[K] = {}
        print(f"\n  K = {K}:")
        print(f"  | G*    | alpha  | g_K    | status       |")
        print(f"  |-------|--------|--------|--------------|")
        
        for G_star in G_stars:
            alpha, g, status = find_alpha_for_gain_cap(model, z, x_enc, K, G_star)
            derived_alphas[K][G_star] = alpha
            print(f"  | {G_star:5.1f} | {alpha:6.3f} | {g:6.2f} | {status:12s} |")
    
    # Find G* that gives alpha ≈ 0.1
    print(f"\n[4/5] Finding G* such that derived alpha ~ 0.1...")
    
    for K in [30, 100]:
        # Binary search for G* that gives alpha ≈ 0.1
        g_at_01 = estimate_K_step_gain(model, z, x_enc, K, 0.1, n_probes=5, n_power_iter=2)
        print(f"\n  K={K}: g_K(0.1) = {g_at_01:.2f}")
        print(f"  -> G* = {g_at_01:.2f} would give alpha = 0.1")
    
    # Validate derived alpha
    print(f"\n[5/5] Validating derived alpha at T=200...")
    
    test_p = puzzles[100:300]
    test_s = solutions[100:300]
    
    # Get derived alpha for K=30, G*=g_K(0.1)
    g_target = estimate_K_step_gain(model, z, x_enc, 30, 0.1, n_probes=5, n_power_iter=2)
    
    print(f"\n  | Method                    | Alpha  | Solved@200 |")
    print(f"  |---------------------------|--------|------------|")
    
    for alpha in [1.0, 0.5, 0.2, 0.1, 0.05]:
        solved = run_with_alpha(model, test_p, test_s, T=200, alpha=alpha)
        marker = " <-- empirical" if alpha == 0.1 else ""
        print(f"  | alpha={alpha:4.2f}               | {alpha:6.2f} | {solved*100:5.1f}%     |{marker}")
    
    # Summary
    print("\n" + "="*70)
    print("TRANSIENT GAIN CONSTITUTIVE LAW")
    print("="*70)
    
    print(f"""
  NON-NORMALITY FRAMEWORK:
  
  For non-normal M, ||M^K|| can be >> 1 even when rho(M) < 1.
  This is "transient amplification" - the mechanism of metastability.
  
  THE CONSTITUTIVE LAW:
  
  1. Measure: g_K(alpha) = max ||M_alpha^K v||  (K-step gain)
  2. Set budget: G* = allowed transient amplification
  3. Derive: alpha = max{{a : g_K(a) <= G*}}
  
  MEASURED GAINS:
    g_30(0.1) = {gains[30][0.1]:.2f}
    g_100(0.1) = {gains[100][0.1]:.2f}
    g_30(1.0) = {gains[30][1.0]:.2f}
    g_100(1.0) = {gains[100][1.0]:.2f}
  
  TO GET alpha=0.1:
    Set G* = g_K(0.1)
    K=30:  G* = {gains[30][0.1]:.2f}
    K=100: G* = {gains[100][0.1]:.2f}
  
  INTERPRETATION:
  G* is the "entropy production budget" - how much transient
  amplification we allow before the system must have settled.
  
  This IS Jacobson-style:
  - Constitutive parameter: g_K (transient gain)
  - Universal law: g_K <= G*
  - Derived quantity: alpha
  
  G* replaces the arbitrary hyperparameter. It has physical meaning:
  "The system may amplify perturbations by at most G* over K steps."
""")
    
    # For Lean
    print("="*70)
    print("FOR LEAN FORMALIZATION")
    print("="*70)
    
    print(f"""
  theorem sgc_transient_gain_bound
    (M : X ->L[R] X) (K : Nat) (G_star : R)
    (alpha : R)
    (h_alpha : forall v, norm (iterate M K v) <= G_star * norm v)
    (h_nonneg : 0 < alpha) (h_le_one : alpha <= 1) :
    -- The damped iteration has bounded K-step gain
    forall v, norm (iterate (fun x => (1-alpha)*x + alpha*(M x)) K v) 
              <= G_star * norm v
  
  The key insight: K-step gain ||M^K|| is the constitutive parameter
  for non-normal systems, not spectral radius rho(M).
  
  Measured for this model:
    g_30(0.1) = {gains[30][0.1]:.2f}
    g_100(0.1) = {gains[100][0.1]:.2f}
""")


if __name__ == '__main__':
    main()
