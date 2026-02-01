#!/usr/bin/env python3
"""
SGC Phase 1: Grokking Experiment (Lean-Aligned)
================================================

This experiment validates the Phase 1 Hybrid Architecture by testing the
SGC theory on the classic "Grokking" task: modular addition (a + b mod p).

**Key Alignment with Lean Formalization (RenormalizationDynamics.lean):**

1. ConflictRatio uses SQUARED norms:
   C(S, g) = ||P_S g||² / ||g||²
   
2. DefectGatedConsolidationCriterion (Stiff AND Stable):
   - Stiff: v^T F v / v^T v > τ_stiff (high Fisher eigenvalue)
   - Stable: |v · g| / ||v|| < ε_stable (low gradient projection)
   
3. Triple Crossing Signature:
   - Rigidity: Tr(P_S F P_S) rises
   - Conflict: ConflictRatio drops
   - Dimension: k (number of consolidated directions) changes

**The Grokking Phenomenon:**
The model initially memorizes training data (high train acc, low test acc),
then suddenly "groks" the underlying structure (test acc jumps).

SGC predicts this corresponds to:
- Phase 1: High ConflictRatio (gradient fights random S)
- Phase Transition: S reorganizes to align with Fisher eigendirections
- Phase 2: Low ConflictRatio, High Rigidity (stable structure found)

Author: SGC Project | License: Apache 2.0
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import argparse
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from pathlib import Path
from datetime import datetime
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

# TensorBoard for browser-based monitoring
from torch.utils.tensorboard import SummaryWriter


# ═══════════════════════════════════════════════════════════════════════════════
# PART I: SGC METRICS (Lean-Aligned)
# These match the definitions in RenormalizationDynamics.lean exactly
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class SGCMetrics:
    """Container for SGC Phase 1 metrics, matching Lean formalization.
    
    Phase-1c Update: Scale-invariant geometry
    - Stiffness uses RELATIVE threshold (tau_rel * lambda_max)
    - Normalized spectrum logged for scale-invariant analysis
    
    NOTE: This is SCALE-INVARIANCE (invariant to F → αF), not full Fisher-Rao
    invariance (which would require reparameterization invariance).
    """
    conflict_ratio: float          # ||P_S g||² / ||g||² (SQUARED norms)
    fisher_rigidity: float         # Tr(P_S F P_S) - absolute scale
    fisher_rigidity_normalized: float  # Rigidity / Tr(F) - scale-invariant
    complexity_cost: int           # dim(S) = k
    variational_objective: float   # Rigidity - λ·Cost
    
    # Defect-Gated Consolidation diagnostics
    num_stiff_directions: int      # Directions with λ > tau_rel * λ_max
    num_stable_directions: int     # Directions with |v·g|/(||g||) < eps_rel
    num_consolidated: int          # Directions that are BOTH stiff AND stable
    
    # Scale-free spectrum diagnostics (Phase-1c)
    max_eigenvalue: float = 0.0    # λ_max (absolute scale)
    trace_fisher: float = 0.0      # Tr(F) = Σλᵢ (total Fisher mass)
    spectral_gap: float = 0.0      # λ₁/λₖ for chosen k (structure indicator)
    normalized_eigenvalues: tuple = ()  # (λᵢ/λ_max) for top eigenvalues
    
    # Legacy/diagnostic fields
    gradient_norm: float = 0.0     # ||g|| for scale reference
    top_eigenvalues: tuple = ()    # Top eigenvalues (absolute scale)
    
    # Estimator identification (Phase-1c: explicit about which Fisher)
    fisher_estimator: str = "empirical_score_covariance"  # SVD of gradients


def compute_conflict_ratio_squared(
    S_basis: torch.Tensor,  # (k, n) - orthonormal basis for S
    g: torch.Tensor,        # (n,) - gradient vector
) -> float:
    """
    ConflictRatio(S, g) = ||P_S g||² / ||g||²
    
    This matches Lean's definition in RenormalizationDynamics.lean:
    ```lean
    noncomputable def ConflictRatio (S : ConsolidatedSubspace n k) (g : Fin n → ℝ) : ℝ :=
      let S_mat := SubspaceMatrix S
      let proj := S_mat.mulVec g
      let proj_sq := ∑ i : Fin k, (proj i)^2
      let g_sq := ∑ i : Fin n, (g i)^2
      if g_sq = 0 then 0 else proj_sq / g_sq
    ```
    
    NOTE: Uses SQUARED norms, not regular norms!
    """
    if S_basis.shape[0] == 0:  # Empty subspace
        return 0.0
    
    g_sq = (g ** 2).sum().item()
    if g_sq == 0:
        return 0.0
    
    # P_S g = S^T (S S^T)^{-1} S g = S^T S g (for orthonormal S)
    proj = S_basis @ g  # (k,) - projection coefficients
    proj_sq = (proj ** 2).sum().item()
    
    return proj_sq / g_sq


def compute_fisher_rigidity(
    S_basis: torch.Tensor,  # (k, n) - orthonormal basis for S
    F: torch.Tensor,        # (n, n) - Fisher information matrix
) -> float:
    """
    FisherRigidity(S) = Tr(P_S F P_S) = Tr(S F S^T)
    
    This matches Lean's definition:
    ```lean
    noncomputable def FisherRigidity (state : RenormalizedState n k) : ℝ :=
      let S_mat := SubspaceMatrix state.S
      let SFS := S_mat * state.F * S_matᵀ
      ∑ i : Fin k, SFS i i
    ```
    """
    if S_basis.shape[0] == 0:
        return 0.0
    
    SFS = S_basis @ F @ S_basis.T  # (k, k)
    return torch.trace(SFS).item()


def compute_fisher_rayleigh_quotient(
    F: torch.Tensor,  # (n, n) - Fisher information matrix
    v: torch.Tensor,  # (n,) - direction vector
) -> float:
    """
    FisherRayleighQuotient(F, v) = (v^T F v) / (v^T v)
    
    This matches Lean's definition:
    ```lean
    noncomputable def FisherRayleighQuotient (F : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
      let vFv := ∑ i, ∑ j, v i * F i j * v j
      let vv := ∑ i, (v i)^2
      if vv = 0 then 0 else vFv / vv
    ```
    """
    vv = (v ** 2).sum().item()
    if vv == 0:
        return 0.0
    
    vFv = (v @ F @ v).item()
    return vFv / vv


def compute_gradient_stability(
    v: torch.Tensor,  # (n,) - direction vector
    g: torch.Tensor,  # (n,) - gradient vector
    eps: float,       # stability threshold
) -> bool:
    """
    GradientStability(v, g, ε) = |v · g| / ||v|| < ε
    
    This matches Lean's definition:
    ```lean
    noncomputable def GradientStability (v g : Fin n → ℝ) (eps : ℝ) : Prop :=
      let v_dot_g := |∑ i, v i * g i|
      let v_norm := Real.sqrt (∑ i, (v i)^2)
      v_norm ≠ 0 → v_dot_g / v_norm < eps
    ```
    """
    v_norm = torch.norm(v).item()
    if v_norm == 0:
        return True  # Trivially stable
    
    v_dot_g = abs(torch.dot(v, g).item())
    return (v_dot_g / v_norm) < eps


def defect_gated_consolidation_criterion(
    F: torch.Tensor,   # (n, n) - Fisher information matrix
    v: torch.Tensor,   # (n,) - direction vector
    g: torch.Tensor,   # (n,) - gradient vector
    tau_stiff: float,  # stiffness threshold
    eps_stable: float, # stability threshold
) -> Tuple[bool, bool, bool]:
    """
    DefectGatedConsolidationCriterion: A direction v should be consolidated iff:
    1. FisherSpectralCriterion F v τ (v is stiff)
    2. GradientStability v g ε (v is stable)
    
    This matches Lean's definition:
    ```lean
    def DefectGatedConsolidationCriterion (F : Matrix (Fin n) (Fin n) ℝ)
        (v g : Fin n → ℝ) (tau_stiff eps_stable : ℝ) : Prop :=
      FisherSpectralCriterion F v tau_stiff ∧ GradientStability v g eps_stable
    ```
    
    Returns: (is_stiff, is_stable, should_consolidate)
    """
    rayleigh = compute_fisher_rayleigh_quotient(F, v)
    is_stiff = rayleigh > tau_stiff
    is_stable = compute_gradient_stability(v, g, eps_stable)
    should_consolidate = is_stiff and is_stable
    
    return is_stiff, is_stable, should_consolidate


def compute_sgc_metrics(
    model: nn.Module,
    F: torch.Tensor,           # (n, n) - Fisher information matrix
    g: torch.Tensor,           # (n,) - gradient vector (flattened)
    tau_stiff: float = 0.1,    # stiffness threshold
    eps_stable: float = 0.5,   # stability threshold
    lambda_cost: float = 0.01, # complexity penalty
) -> SGCMetrics:
    """
    Compute all Phase 1 SGC metrics.
    
    The consolidated subspace S is determined by:
    S = span{ eigenvectors of F with eigenvalue > tau_stiff AND GradientStability }
    """
    n = F.shape[0]
    
    # Compute eigendecomposition of Fisher
    eigenvalues, eigenvectors = torch.linalg.eigh(F)
    
    # Sort by eigenvalue descending
    idx = torch.argsort(eigenvalues, descending=True)
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]
    
    # Identify stiff, stable, and consolidated directions
    stiff_mask = eigenvalues > tau_stiff
    num_stiff = stiff_mask.sum().item()
    
    stable_mask = torch.zeros(n, dtype=torch.bool)
    consolidated_mask = torch.zeros(n, dtype=torch.bool)
    
    for i in range(n):
        v = eigenvectors[:, i]
        is_stiff, is_stable, should_consolidate = defect_gated_consolidation_criterion(
            F, v, g, tau_stiff, eps_stable
        )
        stable_mask[i] = is_stable
        consolidated_mask[i] = should_consolidate
    
    num_stable = stable_mask.sum().item()
    num_consolidated = consolidated_mask.sum().item()
    
    # Build S_basis from consolidated directions
    if num_consolidated > 0:
        S_basis = eigenvectors[:, consolidated_mask].T  # (k, n)
    else:
        S_basis = torch.zeros(0, n)
    
    k = S_basis.shape[0]
    
    # Compute metrics
    conflict_ratio = compute_conflict_ratio_squared(S_basis, g)
    fisher_rigidity = compute_fisher_rigidity(S_basis, F)
    variational_objective = fisher_rigidity - lambda_cost * k
    
    return SGCMetrics(
        conflict_ratio=conflict_ratio,
        fisher_rigidity=fisher_rigidity,
        complexity_cost=k,
        variational_objective=variational_objective,
        num_stiff_directions=num_stiff,
        num_stable_directions=num_stable,
        num_consolidated=num_consolidated,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# PART II: FISHER INFORMATION ESTIMATION
# ═══════════════════════════════════════════════════════════════════════════════

def estimate_fisher_diagonal(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str = 'cuda',
    num_samples: int = 200,
) -> torch.Tensor:
    """
    Estimate DIAGONAL of Fisher Information Matrix (GPU-optimized).
    
    Uses diagonal approximation: F_diag ≈ E[g_i^2]
    Much faster than full matrix - O(n) vs O(n^2) memory/compute.
    """
    model.eval()
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    fisher_diag = torch.zeros(n_params, device=device)
    n_used = 0
    
    for x, y in dataloader:
        if n_used >= num_samples:
            break
        x, y = x.to(device), y.to(device)
        
        # Batch processing for speed
        batch_size = min(len(x), num_samples - n_used)
        for i in range(batch_size):
            model.zero_grad()
            logits = model(x[i:i+1])
            log_prob = torch.log_softmax(logits, dim=-1)
            loss = -log_prob[0, y[i]]
            loss.backward()
            
            g = torch.cat([p.grad.flatten() for p in params])
            fisher_diag += g ** 2
            n_used += 1
    
    fisher_diag /= n_used
    return fisher_diag


def get_gradient_vector(model: nn.Module) -> torch.Tensor:
    """Get the current gradient as a flattened vector."""
    params = [p for p in model.parameters() if p.requires_grad]
    grads = []
    for p in params:
        if p.grad is not None:
            grads.append(p.grad.flatten())
        else:
            grads.append(torch.zeros(p.numel(), device=p.device))
    return torch.cat(grads)


def compute_sgc_metrics_fast(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str = 'cuda',
    tau_stiff: float = 0.1,
    eps_stable: float = 0.5,
    lambda_cost: float = 0.01,
    num_fisher_samples: int = 100,
) -> SGCMetrics:
    """
    Fast SGC metrics using diagonal Fisher approximation (GPU-optimized).
    
    This is O(n) instead of O(n^2) for full Fisher matrix.
    """
    # Get Fisher diagonal
    fisher_diag = estimate_fisher_diagonal(model, dataloader, device, num_fisher_samples)
    
    # Get current gradient
    model.zero_grad()
    criterion = nn.CrossEntropyLoss()
    for x, y in dataloader:
        x, y = x.to(device), y.to(device)
        logits = model(x)
        loss = criterion(logits, y)
        loss.backward()
        break
    
    params = [p for p in model.parameters() if p.requires_grad]
    g = torch.cat([p.grad.flatten() for p in params])
    
    # Identify stiff directions (eigenvalue > tau)
    stiff_mask = fisher_diag > tau_stiff
    num_stiff = stiff_mask.sum().item()
    
    # Identify stable directions (low gradient projection)
    g_abs = torch.abs(g)
    stable_mask = g_abs < eps_stable
    num_stable = stable_mask.sum().item()
    
    # Consolidated = stiff AND stable (DefectGatedConsolidationCriterion)
    consolidated_mask = stiff_mask & stable_mask
    num_consolidated = int(consolidated_mask.sum().item())
    
    # Conflict ratio using diagonal approximation
    # ||P_S g||^2 / ||g||^2 where P_S projects onto consolidated directions
    g_sq = (g ** 2).sum().item()
    if g_sq > 0 and num_consolidated > 0:
        proj_sq = ((g * consolidated_mask.float()) ** 2).sum().item()
        conflict_ratio = proj_sq / g_sq
    else:
        conflict_ratio = 0.0
    
    # Rigidity = sum of Fisher eigenvalues in S
    fisher_rigidity = (fisher_diag * consolidated_mask.float()).sum().item()
    
    # Variational objective
    variational_obj = fisher_rigidity - lambda_cost * num_consolidated
    
    return SGCMetrics(
        conflict_ratio=conflict_ratio,
        fisher_rigidity=fisher_rigidity,
        complexity_cost=num_consolidated,
        variational_objective=variational_obj,
        num_stiff_directions=num_stiff,
        num_stable_directions=num_stable,
        num_consolidated=num_consolidated,
    )


def get_gradient_vector_v2(model: nn.Module) -> torch.Tensor:
    """Get the current gradient as a flattened vector (v2 - redundant, keeping for compat)."""
    params = [p for p in model.parameters() if p.requires_grad]
    grads = []
    for p in params:
        if p.grad is not None:
            grads.append(p.grad.flatten())
        else:
            grads.append(torch.zeros(p.numel(), device=p.device))
    return torch.cat(grads)


def compute_sgc_metrics_svd(
    model: nn.Module,
    dataloader: torch.utils.data.DataLoader,
    device: str = 'cuda',
    tau_rel: float = 0.1,
    eps_rel: float = 0.1,
    lambda_cost: float = 0.01,
    num_samples: int = 200,
    max_rank: int = 100,
) -> SGCMetrics:
    """
    Phase-1c: Scale-free SGC metrics using SVD of gradient matrix.
    
    Key insight: For gradient matrix G in R^{M x N}, the empirical Fisher is:
        F = (1/M) G^T G
    The eigenvectors of F are the RIGHT singular vectors of G, and
    eigenvalues are lambda_i = s_i^2 / M where s_i are singular values.
    
    Phase-1c Update: Uses RELATIVE stiffness threshold (scale-invariant)
        Stiff iff lambda_i > tau_rel * lambda_max
    This ensures consolidation criterion is invariant to Fisher scaling.
    
    Args:
        model: Neural network model
        dataloader: Training data loader
        device: Compute device
        tau_rel: RELATIVE stiffness threshold (lambda > tau_rel * lambda_max)
        eps_rel: Relative stability threshold (cosine-based, scale-invariant)
        lambda_cost: Complexity penalty coefficient
        num_samples: Number of gradient samples to collect
        max_rank: Maximum rank for truncated SVD (for efficiency)
    """
    model.eval()
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    # Collect per-sample gradients into matrix G (M x N)
    gradients = []
    n_collected = 0
    
    for x, y in dataloader:
        if n_collected >= num_samples:
            break
        x, y = x.to(device), y.to(device)
        
        batch_size = min(len(x), num_samples - n_collected)
        for i in range(batch_size):
            model.zero_grad()
            logits = model(x[i:i+1])
            log_prob = torch.log_softmax(logits, dim=-1)
            loss = -log_prob[0, y[i]]
            loss.backward()
            
            g = torch.cat([p.grad.flatten() for p in params])
            gradients.append(g)
            n_collected += 1
    
    # Stack into gradient matrix G: (M x N)
    G = torch.stack(gradients, dim=0)  # (M, N)
    M = G.shape[0]
    
    # Compute mean gradient (for stability test and conflict ratio)
    g_mean = G.mean(dim=0)  # (N,)
    g_norm = torch.norm(g_mean)
    
    # SVD of G: G = U @ diag(s) @ V^T
    # For tall-skinny matrices, CPU SVD can be faster than GPU
    # Move to CPU for SVD if matrix is large
    if n_params > 10000:
        G_cpu = G.cpu()
        U, s, Vh = torch.linalg.svd(G_cpu, full_matrices=False)
        V = Vh.T  # Right singular vectors (N x M)
        s = s.to(device)
        V = V.to(device)
    else:
        U, s, Vh = torch.linalg.svd(G, full_matrices=False)
        V = Vh.T  # (N x min(M,N))
    
    # Fisher eigenvalues: lambda_i = s_i^2 / M
    eigenvalues = (s ** 2) / M
    
    # Truncate to max_rank for efficiency
    k_max = min(max_rank, len(eigenvalues))
    eigenvalues = eigenvalues[:k_max]
    V = V[:, :k_max]  # (N x k_max) - top k eigenvectors
    
    # Phase-1c: Compute scale-free spectrum diagnostics
    max_eig = eigenvalues[0].item() if len(eigenvalues) > 0 else 0.0
    trace_fisher = eigenvalues.sum().item()
    
    # Normalized eigenvalues (scale-invariant spectrum shape)
    if max_eig > 1e-10:
        normalized_eigs = (eigenvalues / max_eig).tolist()[:10]
    else:
        normalized_eigs = [0.0] * min(10, len(eigenvalues))
    
    # Phase-1c: RELATIVE stiffness threshold (scale-invariant)
    # Stiff iff lambda_i > tau_rel * lambda_max
    # This is invariant to global Fisher scaling (scale-invariance, not full Fisher-Rao)
    stiff_threshold = tau_rel * max_eig if max_eig > 1e-10 else 0.0
    stiff_mask = eigenvalues > stiff_threshold
    num_stiff = int(stiff_mask.sum().item())
    
    # Identify STABLE directions using Lean-aligned stability criterion
    # Lean GradientStability: |v · g| / ||v|| < eps_stable
    # Since V columns are unit vectors from SVD: ||v|| = 1
    # So stability becomes: |v · g| < eps_stable
    #
    # HOWEVER, eps_stable needs to be calibrated to gradient scale.
    # We use eps_rel as a RELATIVE threshold: |v · g| < eps_rel * ||g||
    # This is scale-invariant and matches the INTENT of Lean's stability.
    stable_mask = torch.zeros(k_max, dtype=torch.bool, device=device)
    
    # Compute projection magnitudes for each direction (Lean-aligned)
    # |v · g| for unit vector v
    for i in range(k_max):
        v = V[:, i]  # Unit norm from SVD
        proj_magnitude = torch.abs(torch.dot(v, g_mean)).item()
        # Scale-invariant threshold: compare to fraction of total gradient
        # This is |v · g| / ||g|| < eps_rel, equivalent to cosine < eps_rel
        # But we also store the raw projection for diagnostics
        if g_norm > 1e-10:
            relative_proj = proj_magnitude / g_norm.item()
            stable_mask[i] = relative_proj < eps_rel
        else:
            # If gradient is near-zero, all directions are stable
            stable_mask[i] = True
    
    num_stable = int(stable_mask.sum().item())
    
    # CONSOLIDATED = Stiff AND Stable (DefectGatedConsolidationCriterion)
    consolidated_mask = stiff_mask & stable_mask
    num_consolidated = int(consolidated_mask.sum().item())
    
    # Build consolidated subspace basis S (orthonormal)
    if num_consolidated > 0:
        S_basis = V[:, consolidated_mask]  # (N x k) orthonormal columns
    else:
        S_basis = None
    
    # CONFLICT RATIO: ||P_S g||^2 / ||g||^2
    # P_S g = S @ S^T @ g (orthonormal projection)
    if S_basis is not None and g_norm > 1e-10:
        proj = S_basis @ (S_basis.T @ g_mean)  # (N,)
        proj_norm_sq = torch.dot(proj, proj).item()
        g_norm_sq = (g_norm ** 2).item()
        conflict_ratio = proj_norm_sq / g_norm_sq
    else:
        conflict_ratio = 0.0
    
    # FISHER RIGIDITY: Tr(S^T F S) = sum of eigenvalues in S
    # Since S columns are eigenvectors, Tr(S^T F S) = sum of their eigenvalues
    if num_consolidated > 0:
        fisher_rigidity = eigenvalues[consolidated_mask].sum().item()
    else:
        fisher_rigidity = 0.0
    
    # Phase-1c: Normalized rigidity (scale-invariant)
    # Rigidity / Tr(F) = fraction of total Fisher mass in consolidated subspace
    fisher_rigidity_normalized = fisher_rigidity / trace_fisher if trace_fisher > 1e-10 else 0.0
    
    # Phase-1c: Spectral gap (structure indicator)
    # Gap = λ_k / λ_{k+1} where k = num_stiff (based on stiff_mask, not consolidated)
    # This measures the "cliff" between stiff and sloppy directions in the SPECTRUM.
    # Large gap = clear separation; small gap = no clear structure.
    # 
    # NOTE: We use stiff_mask (pure spectral criterion) not consolidated_mask
    # because we want the spectral gap, independent of gradient stability.
    # 
    # Edge cases:
    # - k=0 (no stiff dirs): gap=1.0 (no structure detected)
    # - k=k_max (all stiff): gap=1.0 (no boundary to measure)
    # - λ_{k+1} ≈ 0: gap=inf (sharp cutoff, but cap at 1000 for logging)
    if num_stiff > 0 and num_stiff < k_max:
        # Gap at the stiffness boundary
        lambda_k = eigenvalues[num_stiff - 1].item()  # Last stiff direction
        lambda_k_plus_1 = eigenvalues[num_stiff].item()  # First sloppy direction
        if lambda_k_plus_1 > 1e-10:
            spectral_gap = lambda_k / lambda_k_plus_1
            spectral_gap = min(spectral_gap, 1000.0)  # Cap for logging sanity
        else:
            spectral_gap = 1000.0  # Effectively infinite gap
    else:
        spectral_gap = 1.0  # No gap if all or none are stiff
    
    # Variational objective: Rigidity - lambda * Cost
    variational_obj = fisher_rigidity - lambda_cost * num_consolidated
    
    # Top eigenvalues (absolute scale, for legacy compatibility)
    top_eigs = tuple(eigenvalues[:5].tolist()) if len(eigenvalues) >= 5 else tuple(eigenvalues.tolist())
    
    return SGCMetrics(
        conflict_ratio=conflict_ratio,
        fisher_rigidity=fisher_rigidity,
        fisher_rigidity_normalized=fisher_rigidity_normalized,
        complexity_cost=num_consolidated,
        variational_objective=variational_obj,
        num_stiff_directions=num_stiff,
        num_stable_directions=num_stable,
        num_consolidated=num_consolidated,
        max_eigenvalue=max_eig,
        trace_fisher=trace_fisher,
        spectral_gap=spectral_gap,
        normalized_eigenvalues=tuple(normalized_eigs),
        gradient_norm=g_norm.item(),
        top_eigenvalues=top_eigs,
        fisher_estimator="empirical_score_covariance",
    )


# ═══════════════════════════════════════════════════════════════════════════════
# PART III: MODULAR ADDITION TASK (Grokking)
# ═══════════════════════════════════════════════════════════════════════════════

class ModularAdditionDataset(torch.utils.data.Dataset):
    """
    Dataset for modular addition: (a, b) -> (a + b) mod p
    
    This is the classic "Grokking" task from Power et al. (2022).
    """
    
    def __init__(self, p: int = 97, train: bool = True, train_fraction: float = 0.3):
        self.p = p
        
        # Generate all pairs
        all_pairs = [(a, b) for a in range(p) for b in range(p)]
        all_labels = [(a + b) % p for a, b in all_pairs]
        
        # Split into train/test
        n_train = int(len(all_pairs) * train_fraction)
        indices = list(range(len(all_pairs)))
        np.random.seed(42)  # Fixed seed for reproducibility
        np.random.shuffle(indices)
        
        if train:
            self.indices = indices[:n_train]
        else:
            self.indices = indices[n_train:]
        
        self.pairs = [all_pairs[i] for i in self.indices]
        self.labels = [all_labels[i] for i in self.indices]
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        label = self.labels[idx]
        # One-hot encode inputs
        x = torch.zeros(2 * self.p)
        x[a] = 1.0
        x[self.p + b] = 1.0
        return x, label


class GrokMLP(nn.Module):
    """
    Simple MLP for modular addition (standard Grokking architecture).
    """
    
    def __init__(self, p: int = 97, hidden_dim: int = 128):
        super().__init__()
        self.p = p
        self.net = nn.Sequential(
            nn.Linear(2 * p, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, p),
        )
    
    def forward(self, x):
        return self.net(x)


# ═══════════════════════════════════════════════════════════════════════════════
# PART IV: TRAINING LOOP WITH SGC MONITORING
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class TrainingState:
    """Container for training state and history."""
    epoch: int
    train_loss: float
    train_acc: float
    test_acc: float
    sgc_metrics: Optional[SGCMetrics]


def train_with_sgc_monitoring(
    model: nn.Module,
    train_loader: torch.utils.data.DataLoader,
    test_loader: torch.utils.data.DataLoader,
    epochs: int = 10000,
    lr: float = 1e-3,
    weight_decay: float = 1.0,  # Important for grokking!
    device: str = 'cpu',
    sgc_interval: int = 100,    # Compute SGC metrics every N epochs
    tau_rel: float = 0.1,       # Phase-1c: RELATIVE stiffness threshold (lambda > tau_rel * lambda_max)
    eps_rel: float = 0.1,       # Cosine stability threshold (scale-invariant)
    lambda_cost: float = 0.01,
    log_dir: str = 'logs/grokking',
    num_svd_samples: int = 200, # Samples for SVD-based Fisher estimation
) -> List[TrainingState]:
    """
    Phase-1c: Train model with scale-free SGC metric monitoring.
    
    Key Phase-1c changes:
    - tau_rel: Relative stiffness threshold (scale-invariant)
    - Logs normalized spectrum diagnostics for scale-invariant geometry analysis
    
    Returns history of training states for analysis.
    """
    model = model.to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    criterion = nn.CrossEntropyLoss()
    
    # Setup TensorBoard
    log_path = Path(log_dir)
    log_path.mkdir(parents=True, exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    writer = SummaryWriter(str(log_path / f"run_{ts}"))
    print(f"TensorBoard logs: {log_path / f'run_{ts}'}")
    print(f"Run: tensorboard --logdir {log_dir}")
    
    history = []
    
    # Track last known SGC metrics for continuous TensorBoard logging
    last_sgc = SGCMetrics(
        conflict_ratio=0.0,
        fisher_rigidity=0.0,
        fisher_rigidity_normalized=0.0,
        complexity_cost=0,
        variational_objective=0.0,
        num_stiff_directions=0,
        num_stable_directions=0,
        num_consolidated=0,
        max_eigenvalue=0.0,
        trace_fisher=0.0,
        spectral_gap=1.0,
        normalized_eigenvalues=(),
        gradient_norm=0.0,
        top_eigenvalues=(),
        fisher_estimator="empirical_score_covariance",
    )
    
    for epoch in range(1, epochs + 1):
        # Training
        model.train()
        total_loss = 0
        correct = 0
        total = 0
        
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            
            optimizer.zero_grad()
            logits = model(x)
            loss = criterion(logits, y)
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item() * len(x)
            correct += (logits.argmax(dim=-1) == y).sum().item()
            total += len(x)
        
        train_loss = total_loss / total
        train_acc = correct / total
        
        # Testing
        model.eval()
        correct = 0
        total = 0
        
        with torch.no_grad():
            for x, y in test_loader:
                x, y = x.to(device), y.to(device)
                logits = model(x)
                correct += (logits.argmax(dim=-1) == y).sum().item()
                total += len(x)
        
        test_acc = correct / total
        
        # Compute SGC metrics periodically (using SVD-based spectral decomposition)
        sgc_metrics = None
        if epoch % sgc_interval == 0 or epoch == 1:
            sgc_metrics = compute_sgc_metrics_svd(
                model, train_loader, device,
                tau_rel=tau_rel,  # Phase-1c: relative threshold
                eps_rel=eps_rel,
                lambda_cost=lambda_cost,
                num_samples=num_svd_samples,
                max_rank=100,
            )
        
        state = TrainingState(
            epoch=epoch,
            train_loss=train_loss,
            train_acc=train_acc,
            test_acc=test_acc,
            sgc_metrics=sgc_metrics,
        )
        history.append(state)
        
        # Update last known SGC metrics if we computed new ones
        if sgc_metrics:
            last_sgc = sgc_metrics
        
        # TensorBoard logging - ALWAYS log all metrics for continuous plots
        # === PERFORMANCE METRICS ===
        writer.add_scalar('Performance/TrainAcc', train_acc * 100, epoch)
        writer.add_scalar('Performance/TestAcc', test_acc * 100, epoch)
        writer.add_scalar('Performance/TrainLoss', train_loss, epoch)
        writer.add_scalar('Performance/GeneralizationGap', (train_acc - test_acc) * 100, epoch)
        
        # === SGC CORE METRICS (Theory-Testing) ===
        # These are the key metrics aligned with Lean formalization
        writer.add_scalar('SGC/ConflictRatio', last_sgc.conflict_ratio, epoch)
        writer.add_scalar('SGC/FisherRigidity', last_sgc.fisher_rigidity, epoch)
        writer.add_scalar('SGC/ConsolidatedDim', last_sgc.num_consolidated, epoch)
        writer.add_scalar('SGC/VariationalObjective', last_sgc.variational_objective, epoch)
        
        # === PHASE-1c: SCALE-FREE METRICS (Fisher-Rao Geometry) ===
        writer.add_scalar('ScaleFree/RigidityNormalized', last_sgc.fisher_rigidity_normalized, epoch)
        writer.add_scalar('ScaleFree/TraceFisher', last_sgc.trace_fisher, epoch)
        writer.add_scalar('ScaleFree/SpectralGap', last_sgc.spectral_gap, epoch)
        # Log top normalized eigenvalues (spectrum shape)
        if last_sgc.normalized_eigenvalues:
            for i, nev in enumerate(last_sgc.normalized_eigenvalues[:5]):
                writer.add_scalar(f'Spectrum/NormEig_{i+1}', nev, epoch)
        
        # === DEFECT-GATED CONSOLIDATION DIAGNOSTICS ===
        writer.add_scalar('Consolidation/NumStiff', last_sgc.num_stiff_directions, epoch)
        writer.add_scalar('Consolidation/NumStable', last_sgc.num_stable_directions, epoch)
        writer.add_scalar('Consolidation/StiffAndStable', last_sgc.num_consolidated, epoch)
        
        # === SPECTRAL DIAGNOSTICS (Absolute Scale) ===
        writer.add_scalar('Spectral/MaxEigenvalue', last_sgc.max_eigenvalue, epoch)
        writer.add_scalar('Spectral/GradientNorm', last_sgc.gradient_norm, epoch)
        
        # === DERIVED METRICS FOR PHASE TRANSITION DETECTION ===
        # Rigidity per dimension (information density)
        if last_sgc.num_consolidated > 0:
            rigidity_per_dim = last_sgc.fisher_rigidity / last_sgc.num_consolidated
        else:
            rigidity_per_dim = 0.0
        writer.add_scalar('Derived/RigidityPerDim', rigidity_per_dim, epoch)
        
        # Conflict-Rigidity ratio (should invert at grokking)
        if last_sgc.fisher_rigidity > 0:
            conflict_rigidity_ratio = last_sgc.conflict_ratio / (last_sgc.fisher_rigidity + 1e-8)
        else:
            conflict_rigidity_ratio = last_sgc.conflict_ratio
        writer.add_scalar('Derived/ConflictRigidityRatio', conflict_rigidity_ratio, epoch)
        
        # Console logging
        if epoch % 100 == 0 or epoch == 1:
            msg = f"Epoch {epoch:5d}: loss={train_loss:.4f}, train={train_acc*100:.1f}%, test={test_acc*100:.1f}%"
            if sgc_metrics:
                msg += f" | C={sgc_metrics.conflict_ratio:.3f}, R_norm={sgc_metrics.fisher_rigidity_normalized:.3f}, k={sgc_metrics.num_consolidated}"
                msg += f" | gap={sgc_metrics.spectral_gap:.2f}, Tr(F)={sgc_metrics.trace_fisher:.4f}"
            print(msg)
        
        # Early stopping if grokked
        if test_acc > 0.99:
            print(f"\n*** GROKKING ACHIEVED at epoch {epoch}! ***")
            writer.add_text('Event', f'Grokking achieved at epoch {epoch}', epoch)
            break
    
    writer.close()
    return history


# ═══════════════════════════════════════════════════════════════════════════════
# PART V: ANALYSIS AND VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

def analyze_grokking(history: List[TrainingState], save_path: str = "grokking_analysis.png"):
    """
    Analyze the grokking trajectory and look for Triple Crossing Signature.
    
    Triple Crossing Signature:
    1. Rigidity rises (Fisher information concentrated)
    2. Conflict drops (gradient aligns with structure)
    3. Dimension changes (k jumps at phase transition)
    """
    epochs = [s.epoch for s in history]
    train_acc = [s.train_acc for s in history]
    test_acc = [s.test_acc for s in history]
    
    # Extract SGC metrics (only from epochs where computed)
    sgc_epochs = [s.epoch for s in history if s.sgc_metrics is not None]
    conflict = [s.sgc_metrics.conflict_ratio for s in history if s.sgc_metrics is not None]
    rigidity = [s.sgc_metrics.fisher_rigidity for s in history if s.sgc_metrics is not None]
    dimension = [s.sgc_metrics.num_consolidated for s in history if s.sgc_metrics is not None]
    variational = [s.sgc_metrics.variational_objective for s in history if s.sgc_metrics is not None]
    
    # Create visualization
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Plot 1: Accuracy curves
    ax1 = axes[0, 0]
    ax1.plot(epochs, train_acc, 'b-', label='Train', alpha=0.7)
    ax1.plot(epochs, test_acc, 'r-', label='Test', alpha=0.7)
    ax1.set_xlabel('Epoch')
    ax1.set_ylabel('Accuracy')
    ax1.set_title('Grokking: Train vs Test Accuracy')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Conflict Ratio (should drop at grokking)
    ax2 = axes[0, 1]
    ax2.plot(sgc_epochs, conflict, 'g-o', markersize=3)
    ax2.set_xlabel('Epoch')
    ax2.set_ylabel('ConflictRatio (squared)')
    ax2.set_title('SGC: Conflict Ratio ||P_S g||² / ||g||²')
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Fisher Rigidity (should rise at grokking)
    ax3 = axes[1, 0]
    ax3.plot(sgc_epochs, rigidity, 'm-o', markersize=3)
    ax3.set_xlabel('Epoch')
    ax3.set_ylabel('Rigidity Tr(P_S F P_S)')
    ax3.set_title('SGC: Fisher Rigidity')
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Consolidated Dimension (should change at phase transition)
    ax4 = axes[1, 1]
    ax4.plot(sgc_epochs, dimension, 'c-o', markersize=3)
    ax4.set_xlabel('Epoch')
    ax4.set_ylabel('k (consolidated directions)')
    ax4.set_title('SGC: Dimension of Consolidated Subspace')
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(save_path, dpi=150)
    print(f"\nAnalysis saved to {save_path}")
    
    # Check for Triple Crossing Signature
    print("\n" + "="*70)
    print("TRIPLE CROSSING SIGNATURE ANALYSIS")
    print("="*70)
    
    if len(conflict) > 1:
        # Find max test acc jump
        test_accs = [s.test_acc for s in history if s.sgc_metrics is not None]
        max_jump_idx = 0
        max_jump = 0
        for i in range(1, len(test_accs)):
            jump = test_accs[i] - test_accs[i-1]
            if jump > max_jump:
                max_jump = jump
                max_jump_idx = i
        
        if max_jump > 0.1:  # Significant jump
            print(f"\n[OK] Phase transition detected at epoch {sgc_epochs[max_jump_idx]}")
            print(f"  Test accuracy jump: {test_accs[max_jump_idx-1]*100:.1f}% -> {test_accs[max_jump_idx]*100:.1f}%")
            
            # Check conflict drop
            if max_jump_idx > 0 and conflict[max_jump_idx] < conflict[max_jump_idx-1]:
                print(f"  [OK] Conflict DROPPED: {conflict[max_jump_idx-1]:.3f} -> {conflict[max_jump_idx]:.3f}")
            else:
                print(f"  [--] Conflict did not drop as expected")
            
            # Check rigidity rise
            if max_jump_idx > 0 and rigidity[max_jump_idx] > rigidity[max_jump_idx-1]:
                print(f"  [OK] Rigidity ROSE: {rigidity[max_jump_idx-1]:.1f} -> {rigidity[max_jump_idx]:.1f}")
            else:
                print(f"  [--] Rigidity did not rise as expected")
            
            # Check dimension change
            if max_jump_idx > 0 and dimension[max_jump_idx] != dimension[max_jump_idx-1]:
                print(f"  [OK] Dimension CHANGED: {dimension[max_jump_idx-1]} -> {dimension[max_jump_idx]}")
            else:
                print(f"  ~ Dimension stayed constant at {dimension[max_jump_idx]}")
        else:
            print("\n[--] No significant phase transition detected (test acc jump < 10%)")
    
    return fig


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="SGC Phase 1: Grokking Experiment")
    parser.add_argument('--p', type=int, default=97, help='Prime for modular addition')
    parser.add_argument('--hidden_dim', type=int, default=128, help='MLP hidden dimension')
    parser.add_argument('--epochs', type=int, default=5000, help='Training epochs')
    parser.add_argument('--lr', type=float, default=1e-3, help='Learning rate')
    parser.add_argument('--weight_decay', type=float, default=1.0, help='Weight decay (important for grokking)')
    parser.add_argument('--train_fraction', type=float, default=0.3, help='Fraction of data for training')
    parser.add_argument('--batch_size', type=int, default=512, help='Batch size')
    parser.add_argument('--sgc_interval', type=int, default=100, help='SGC metrics computation interval')
    parser.add_argument('--tau_rel', type=float, default=0.01, help='Phase-1c: Relative stiffness threshold (lambda > tau_rel * lambda_max). Start with 0.01-0.1; tune to keep k in 10-100 range during formation.')
    parser.add_argument('--eps_rel', type=float, default=0.1, help='Cosine stability threshold (scale-invariant)')
    parser.add_argument('--num_svd_samples', type=int, default=200, help='Samples for SVD-based Fisher estimation')
    parser.add_argument('--lambda_cost', type=float, default=0.01, help='Complexity cost')
    parser.add_argument('--device', type=str, default='cuda' if torch.cuda.is_available() else 'cpu')
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--log_dir', type=str, default='logs/grokking', help='TensorBoard log directory')
    args = parser.parse_args()
    
    print("="*70)
    print("SGC PHASE 1: GROKKING EXPERIMENT (Lean-Aligned)")
    print("="*70)
    
    # GPU verification
    if torch.cuda.is_available():
        gpu_name = torch.cuda.get_device_name(0)
        gpu_mem = torch.cuda.get_device_properties(0).total_memory / 1e9
        print(f"\nGPU: {gpu_name} ({gpu_mem:.1f} GB)")
        args.device = 'cuda'  # Force CUDA if available
    else:
        print("\nWARNING: No GPU detected, using CPU (will be slow)")
    
    print(f"\nConfiguration:")
    print(f"  Task: Modular addition mod {args.p}")
    print(f"  Model: MLP with {args.hidden_dim} hidden units")
    print(f"  Training: {args.epochs} epochs, lr={args.lr}, wd={args.weight_decay}")
    print(f"  SGC thresholds: tau_rel={args.tau_rel} (relative), eps_rel={args.eps_rel}")
    print(f"  SVD samples: {args.num_svd_samples}")
    print(f"  TensorBoard: {args.log_dir}")
    print(f"  Device: {args.device}")
    print()
    
    # Set seed
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    
    # Create datasets
    train_dataset = ModularAdditionDataset(args.p, train=True, train_fraction=args.train_fraction)
    test_dataset = ModularAdditionDataset(args.p, train=False, train_fraction=args.train_fraction)
    
    print(f"Dataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=args.batch_size, shuffle=True)
    test_loader = torch.utils.data.DataLoader(test_dataset, batch_size=args.batch_size, shuffle=False)
    
    # Create model
    model = GrokMLP(args.p, args.hidden_dim)
    n_params = sum(p.numel() for p in model.parameters())
    print(f"Model parameters: {n_params:,}")
    print()
    
    # Train with SGC monitoring
    print("Training with SGC monitoring...")
    print("-"*70)
    history = train_with_sgc_monitoring(
        model, train_loader, test_loader,
        epochs=args.epochs,
        lr=args.lr,
        weight_decay=args.weight_decay,
        device=args.device,
        sgc_interval=args.sgc_interval,
        tau_rel=args.tau_rel,  # Phase-1c: relative threshold
        eps_rel=args.eps_rel,
        lambda_cost=args.lambda_cost,
        log_dir=args.log_dir,
        num_svd_samples=args.num_svd_samples,
    )
    
    # Analyze results
    analyze_grokking(history)
    
    print("\n" + "="*70)
    print("EXPERIMENT COMPLETE")
    print("="*70)


if __name__ == "__main__":
    main()
