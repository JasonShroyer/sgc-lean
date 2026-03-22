"""
Diagnostic: Why is kappa_contract always ~0?

HYPOTHESIS: During heat phase with noise injection, defect CANNOT contract
because we're actively adding energy to the tail subspace.

The theory says: d_{t+1} <= (1 - kappa*eta) * d_t
But this assumes we're NOT injecting noise. During heat, we ARE injecting noise.

So kappa_contract = 0 during heat is CORRECT - the theory applies to quench phase.

Let's verify this by computing defect trajectory.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math

# Minimal model
class SimpleMLP(nn.Module):
    def __init__(self, d=64):
        super().__init__()
        self.fc1 = nn.Linear(d, d)
        self.fc2 = nn.Linear(d, d)
    
    def forward(self, x):
        return self.fc2(F.relu(self.fc1(x)))


def compute_defect(W: torch.Tensor, k: int = None) -> float:
    """Compute tail energy ratio as defect proxy."""
    S = torch.linalg.svdvals(W)
    S2 = S ** 2
    total = S2.sum().item()
    if total < 1e-10:
        return 1.0
    if k is None:
        cumsum = torch.cumsum(S2, dim=0)
        k = (cumsum < 0.9 * total).sum().item() + 1
    tail = S2[k:].sum().item() if k < len(S) else 0.0
    return math.sqrt(tail / total)


def test_defect_under_noise():
    """Test: Does defect contract when we inject noise?"""
    print("=" * 60)
    print("TEST 1: Defect behavior under noise injection")
    print("=" * 60)
    
    torch.manual_seed(42)
    model = SimpleMLP(d=64)
    
    # Get initial defect
    W = model.fc1.weight.data
    d0 = compute_defect(W)
    print(f"Initial defect: {d0:.4f}")
    
    # Inject noise and measure defect
    noise_scale = 0.1
    defects = [d0]
    
    for i in range(10):
        with torch.no_grad():
            noise = torch.randn_like(model.fc1.weight) * noise_scale
            model.fc1.weight.add_(noise)
        
        d = compute_defect(model.fc1.weight.data)
        defects.append(d)
        ratio = d / defects[-2]
        print(f"  Step {i+1}: defect = {d:.4f}, ratio = {ratio:.4f} {'(contracting)' if ratio < 1 else '(expanding)'}")
    
    print(f"\nConclusion: Under noise, defect {'contracts' if defects[-1] < d0 else 'does NOT contract'}")


def test_defect_under_gradient():
    """Test: Does defect contract when we do gradient descent (no noise)?"""
    print("\n" + "=" * 60)
    print("TEST 2: Defect behavior under gradient descent (no noise)")
    print("=" * 60)
    
    torch.manual_seed(42)
    model = SimpleMLP(d=64)
    
    # Simple target: identity-like behavior
    target = torch.randn(64, 64)
    
    optimizer = torch.optim.SGD(model.parameters(), lr=0.01)
    
    W = model.fc1.weight.data
    d0 = compute_defect(W)
    print(f"Initial defect: {d0:.4f}")
    
    defects = [d0]
    
    for i in range(10):
        x = torch.randn(32, 64)
        y = x @ target.T  # Target output
        
        optimizer.zero_grad()
        out = model(x)
        loss = F.mse_loss(out, y)
        loss.backward()
        optimizer.step()
        
        d = compute_defect(model.fc1.weight.data)
        defects.append(d)
        ratio = d / defects[-2]
        print(f"  Step {i+1}: defect = {d:.4f}, ratio = {ratio:.4f}, loss = {loss.item():.4f}")
    
    print(f"\nConclusion: Under gradient descent, defect {'contracts' if defects[-1] < d0 else 'does NOT contract'}")


def test_kappa_contract_calculation():
    """Test: Is kappa_contract formula correct?"""
    print("\n" + "=" * 60)
    print("TEST 3: kappa_contract formula verification")
    print("=" * 60)
    
    # If d_{k+1} = exp(-kappa * Eta) * d_k
    # Then kappa = -log(d_{k+1}/d_k) / Eta
    
    d_prev = 0.5
    d_curr = 0.4  # 20% contraction
    Eta = 1.0
    
    ratio = d_curr / d_prev
    kappa = -math.log(ratio) / Eta
    
    print(f"d_prev = {d_prev}, d_curr = {d_curr}, Eta = {Eta}")
    print(f"ratio = {ratio:.4f}")
    print(f"kappa = -log({ratio:.4f}) / {Eta} = {kappa:.4f}")
    
    # Verify: d_curr should equal exp(-kappa * Eta) * d_prev
    d_reconstructed = math.exp(-kappa * Eta) * d_prev
    print(f"Verification: exp(-{kappa:.4f} * {Eta}) * {d_prev} = {d_reconstructed:.4f}")
    print(f"Match: {abs(d_reconstructed - d_curr) < 1e-10}")
    
    # What if defect increases?
    d_curr_up = 0.6
    ratio_up = d_curr_up / d_prev
    print(f"\nIf defect INCREASES: d_curr = {d_curr_up}")
    print(f"ratio = {ratio_up:.4f} >= 1.0 -> kappa = 0 (correct!)")


def test_why_phase62_defect_is_zero():
    """Test: Why does Phase-6.2 show defect = 0.000?"""
    print("\n" + "=" * 60)
    print("TEST 4: Phase-6.2 defect = 0.000 investigation")
    print("=" * 60)
    
    # The Phase-6.2 computes defect from hidden layer activations, not weights
    # Let's check what happens
    
    torch.manual_seed(42)
    
    # Simulate hidden activations
    H = torch.randn(500, 64)  # 500 samples, 64 hidden dims
    
    # SVD-based defect: tail energy ratio
    _, S, _ = torch.linalg.svd(H, full_matrices=False)
    S_norm = S / (S.sum() + 1e-10)
    n = len(S)
    tail_start = n // 2
    tail_energy = S_norm[tail_start:].sum().item()
    
    print(f"Hidden activation SVD:")
    print(f"  Shape: {H.shape}")
    print(f"  n_sv = {n}, tail_start = {tail_start}")
    print(f"  tail_energy (defect proxy) = {tail_energy:.4f}")
    
    # What if we normalize S by sum instead of S.sum()?
    # The Phase-6.2 code does: S = S / (S.sum() + 1e-10) which makes it a distribution
    # Then tail_energy = S[tail_start:].sum() which is small but not zero
    
    print(f"\n  Top 5 singular values (normalized): {S_norm[:5].numpy()}")
    print(f"  Bottom 5 singular values (normalized): {S_norm[-5:].numpy()}")


def test_the_real_issue():
    """The real issue: kappa_contract measures WEIGHT defect, but should measure CLOSURE defect."""
    print("\n" + "=" * 60)
    print("TEST 5: The Real Issue - What should kappa measure?")
    print("=" * 60)
    
    print("""
INSIGHT: We have TWO different defects!

1. WEIGHT DEFECT: Tail energy in weight SVD
   - Measures "how much of the weight matrix is in low-rank structure"
   - During heat: noise adds energy to ALL directions -> defect may INCREASE
   - During quench: gradient descent finds structure -> defect DECREASES

2. CLOSURE DEFECT: How well does Pi o f o Pi = Pi o f hold?
   - Measures "how lumpable is the representation"
   - This is what the theory actually cares about!
   
The Contraction Lemma says:
   ||Pi f(x) - Pi f(y)||  <=  (1 - kappa*eta) * ||x - y||
   
This is about the DYNAMICS contracting, not the weight spectrum!

Current kappa_contract measures weight tail contraction.
But the theory is about distance contraction in representation space.

FIX: We should measure kappa from how fast pairs of points converge,
not from how the weight spectrum changes.
""")


if __name__ == "__main__":
    test_defect_under_noise()
    test_defect_under_gradient()
    test_kappa_contract_calculation()
    test_why_phase62_defect_is_zero()
    test_the_real_issue()
