"""
Analog Modular Arithmetic: Floating-Point Noise for Richer Exploration

The insight: Pure modular arithmetic is "too perfect" - the model sees only
exact integers in a discrete universe. This may prevent it from learning
a generalized world model that can "think outside the box."

Solution: Dequantize inputs to floating-point with small noise, while
keeping exact integer labels. The model must learn to:
1. Filter the noise (form a Markov blanket)
2. Discover the discrete structure (crystallize)
3. Snap to exact algebraic rules (grok)

This creates a richer geometry where:
- 3.0008 is "close to" 3.000 but not exact
- The model learns an internal discretizer/quantizer
- Near-misses carry graded information (soft targets option)

Author: SGC Research Team
Date: February 4, 2026
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
import math
from typing import Tuple, Optional, Literal
from dataclasses import dataclass


@dataclass
class AnalogModularConfig:
    """Configuration for analog modular arithmetic dataset."""
    
    # Modular arithmetic parameters
    p: int = 97                          # Prime modulus
    operation: str = 'add'               # 'add', 'sub', 'mul', 'div'
    
    # Analog noise parameters
    input_noise_std: float = 0.1         # Gaussian noise on inputs
    use_phase_encoding: bool = False     # Use sin/cos on mod-p circle
    phase_noise_std: float = 0.05        # Noise on phase encoding
    
    # Soft target parameters (Von Mises / wrapped Gaussian)
    use_soft_targets: bool = False       # Soft cyclic targets
    target_concentration: float = 10.0   # Von Mises concentration (higher = sharper)
    
    # Dataset parameters
    train_fraction: float = 0.3          # Fraction of pairs for training
    seed: int = 42


class AnalogModularDataset(torch.utils.data.Dataset):
    """
    Modular arithmetic with floating-point dequantization.
    
    Creates a "richer universe" where:
    - Inputs are noisy floats centered on integers
    - Labels are exact integer residues (or soft cyclic distributions)
    - The model must learn to filter noise and discover discrete structure
    """
    
    def __init__(self, config: AnalogModularConfig, split: str = 'train'):
        self.config = config
        self.p = config.p
        self.operation = config.operation
        self.split = split
        
        # Generate all pairs
        torch.manual_seed(config.seed)
        np.random.seed(config.seed)
        
        all_pairs = [(a, b) for a in range(self.p) for b in range(self.p)]
        
        # For division, exclude b=0
        if self.operation == 'div':
            all_pairs = [(a, b) for a, b in all_pairs if b != 0]
        
        # Shuffle and split
        np.random.shuffle(all_pairs)
        n_train = int(len(all_pairs) * config.train_fraction)
        
        if split == 'train':
            self.pairs = all_pairs[:n_train]
        else:
            self.pairs = all_pairs[n_train:]
        
        # Precompute targets
        self.targets = [self._compute_target(a, b) for a, b in self.pairs]
    
    def _compute_target(self, a: int, b: int) -> int:
        """Compute exact modular arithmetic result."""
        if self.operation == 'add':
            return (a + b) % self.p
        elif self.operation == 'sub':
            return (a - b) % self.p
        elif self.operation == 'mul':
            return (a * b) % self.p
        elif self.operation == 'div':
            # Modular multiplicative inverse
            b_inv = pow(b, self.p - 2, self.p)  # Fermat's little theorem
            return (a * b_inv) % self.p
        else:
            raise ValueError(f"Unknown operation: {self.operation}")
    
    def _encode_input(self, a: int, b: int) -> torch.Tensor:
        """
        Encode inputs with optional dequantization/noise.
        
        Options:
        1. Direct float + noise: [a + noise, b + noise]
        2. Phase encoding: [cos(2pi*a/p), sin(2pi*a/p), cos(2pi*b/p), sin(2pi*b/p)]
        """
        if self.config.use_phase_encoding:
            # Phase encoding on mod-p circle
            theta_a = 2 * math.pi * a / self.p
            theta_b = 2 * math.pi * b / self.p
            
            # Add phase noise
            if self.config.phase_noise_std > 0:
                theta_a += np.random.normal(0, self.config.phase_noise_std)
                theta_b += np.random.normal(0, self.config.phase_noise_std)
            
            return torch.tensor([
                math.cos(theta_a), math.sin(theta_a),
                math.cos(theta_b), math.sin(theta_b)
            ], dtype=torch.float32)
        else:
            # Direct float encoding with noise
            a_noisy = float(a) + np.random.normal(0, self.config.input_noise_std)
            b_noisy = float(b) + np.random.normal(0, self.config.input_noise_std)
            
            # Normalize to [0, 1] range (roughly)
            a_norm = a_noisy / self.p
            b_norm = b_noisy / self.p
            
            return torch.tensor([a_norm, b_norm], dtype=torch.float32)
    
    def _encode_target(self, target: int) -> torch.Tensor:
        """
        Encode target as one-hot or soft cyclic distribution.
        
        Soft targets use Von Mises (circular Gaussian) centered at correct residue.
        """
        if not self.config.use_soft_targets:
            # Standard one-hot
            return torch.tensor(target, dtype=torch.long)
        else:
            # Von Mises soft target on mod-p circle
            kappa = self.config.target_concentration
            theta_target = 2 * math.pi * target / self.p
            
            # Compute Von Mises PDF at each residue
            probs = torch.zeros(self.p)
            for i in range(self.p):
                theta_i = 2 * math.pi * i / self.p
                # Von Mises: exp(kappa * cos(theta - mu)) / (2*pi*I_0(kappa))
                probs[i] = math.exp(kappa * math.cos(theta_i - theta_target))
            
            # Normalize
            probs = probs / probs.sum()
            return probs
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        target = self.targets[idx]
        
        x = self._encode_input(a, b)
        y = self._encode_target(target)
        
        return x, y


class AnalogGrokMLP(nn.Module):
    """
    MLP for analog modular arithmetic with hooks for closure defect.
    
    The model must learn to:
    1. Filter input noise (blanket formation)
    2. Discover discrete structure (crystallization)
    3. Output exact residue (grokking)
    """
    
    def __init__(self, input_dim: int, hidden_dim: int, output_dim: int, num_layers: int = 2):
        super().__init__()
        
        self.input_dim = input_dim
        self.hidden_dim = hidden_dim
        self.output_dim = output_dim
        
        # Build layers
        layers = []
        in_dim = input_dim
        for i in range(num_layers):
            layers.append(nn.Linear(in_dim, hidden_dim))
            layers.append(nn.ReLU())
            in_dim = hidden_dim
        
        self.hidden_layers = nn.Sequential(*layers)
        self.output_layer = nn.Linear(hidden_dim, output_dim)
        
        # Store intermediate activations for closure defect computation
        self._hidden_activations = None
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        h = self.hidden_layers(x)
        self._hidden_activations = h  # Store for closure defect
        return self.output_layer(h)
    
    def get_hidden(self, x: torch.Tensor) -> torch.Tensor:
        """Get hidden activations without output layer."""
        return self.hidden_layers(x)
    
    def get_output_from_hidden(self, h: torch.Tensor) -> torch.Tensor:
        """Apply output layer to hidden activations."""
        return self.output_layer(h)


class EmbeddingGrokMLP(nn.Module):
    """
    MLP with learned embeddings for modular arithmetic - matches original grokking setup.
    
    Key difference from AnalogGrokMLP: uses discrete embeddings for integers,
    which enables the model to learn rich representations that can grok.
    
    Optional: Add noise to embeddings for the "analog world" experiment.
    """
    
    def __init__(self, 
                 vocab_size: int,       # p (the modulus)
                 embed_dim: int = 128,
                 hidden_dim: int = 128,
                 output_dim: int = None,  # Defaults to vocab_size
                 num_layers: int = 2,
                 embed_noise: float = 0.0):  # Optional noise on embeddings
        super().__init__()
        
        self.vocab_size = vocab_size
        self.embed_dim = embed_dim
        self.hidden_dim = hidden_dim
        self.output_dim = output_dim or vocab_size
        self.embed_noise = embed_noise
        
        # Embeddings for a and b
        self.embed_a = nn.Embedding(vocab_size, embed_dim)
        self.embed_b = nn.Embedding(vocab_size, embed_dim)
        
        # Hidden layers (input is concatenated embeddings)
        layers = []
        in_dim = embed_dim * 2
        for i in range(num_layers):
            layers.append(nn.Linear(in_dim, hidden_dim))
            layers.append(nn.ReLU())
            in_dim = hidden_dim
        
        self.hidden_layers = nn.Sequential(*layers)
        self.output_layer = nn.Linear(hidden_dim, self.output_dim)
        
        self._hidden_activations = None
        self._embeddings = None
    
    def forward(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """
        Forward pass.
        
        Args:
            a: Integer tensor of shape (B,) with values in [0, vocab_size)
            b: Integer tensor of shape (B,) with values in [0, vocab_size)
        
        Returns:
            Logits of shape (B, output_dim)
        """
        # Get embeddings
        e_a = self.embed_a(a)  # (B, embed_dim)
        e_b = self.embed_b(b)  # (B, embed_dim)
        
        # Add noise during training if specified
        if self.training and self.embed_noise > 0:
            e_a = e_a + torch.randn_like(e_a) * self.embed_noise
            e_b = e_b + torch.randn_like(e_b) * self.embed_noise
        
        # Concatenate
        x = torch.cat([e_a, e_b], dim=-1)  # (B, 2 * embed_dim)
        self._embeddings = x
        
        # Hidden layers
        h = self.hidden_layers(x)
        self._hidden_activations = h
        
        # Output
        return self.output_layer(h)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get hidden activations."""
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        x = torch.cat([e_a, e_b], dim=-1)
        return self.hidden_layers(x)
    
    def get_output_from_hidden(self, h: torch.Tensor) -> torch.Tensor:
        """Apply output layer to hidden activations."""
        return self.output_layer(h)


class EmbeddingModularDataset(torch.utils.data.Dataset):
    """
    Modular arithmetic dataset that returns integer indices for embeddings.
    
    This is the standard setup for grokking experiments.
    """
    
    def __init__(self, p: int, operation: str = 'add', 
                 train_fraction: float = 0.3, split: str = 'train', seed: int = 42):
        self.p = p
        self.operation = operation
        
        torch.manual_seed(seed)
        np.random.seed(seed)
        
        # Generate all pairs
        all_pairs = [(a, b) for a in range(p) for b in range(p)]
        
        # Exclude b=0 for division
        if operation == 'div':
            all_pairs = [(a, b) for a, b in all_pairs if b != 0]
        
        np.random.shuffle(all_pairs)
        n_train = int(len(all_pairs) * train_fraction)
        
        if split == 'train':
            self.pairs = all_pairs[:n_train]
        else:
            self.pairs = all_pairs[n_train:]
        
        self.targets = [self._compute(a, b) for a, b in self.pairs]
    
    def _compute(self, a: int, b: int) -> int:
        if self.operation == 'add':
            return (a + b) % self.p
        elif self.operation == 'sub':
            return (a - b) % self.p
        elif self.operation == 'mul':
            return (a * b) % self.p
        elif self.operation == 'div':
            b_inv = pow(b, self.p - 2, self.p)
            return (a * b_inv) % self.p
        raise ValueError(f"Unknown op: {self.operation}")
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        y = self.targets[idx]
        return torch.tensor(a, dtype=torch.long), torch.tensor(b, dtype=torch.long), torch.tensor(y, dtype=torch.long)


def compute_layerwise_closure_defect(
    model: AnalogGrokMLP,
    hidden_states: torch.Tensor,
    k: Optional[int] = None,
    return_components: bool = False
) -> float:
    """
    Compute proper layerwise closure defect: ||Pi g(h) - Pi g(Pi h)||
    
    This measures whether the DYNAMICS are self-consistent on the coarse
    subspace, not just whether the representation is low-dimensional.
    
    Args:
        model: The MLP model
        hidden_states: Hidden activations h (B, D)
        k: Number of top principal components for Pi (auto if None)
        return_components: Also return individual components
    
    Returns:
        Closure defect (0 = perfect closure, higher = more leakage)
    """
    with torch.no_grad():
        B, D = hidden_states.shape
        
        # SVD to get principal components
        U, S, Vh = torch.linalg.svd(hidden_states, full_matrices=False)
        
        # Auto-select k based on 90% energy
        if k is None:
            S2 = S ** 2
            cumsum = torch.cumsum(S2, dim=0)
            total = S2.sum()
            k = (cumsum < 0.9 * total).sum().item() + 1
            k = max(1, min(k, D - 1))
        
        # Projector Pi onto top-k subspace
        # Pi(h) = U[:, :k] @ U[:, :k].T @ h.T  (for each sample)
        # Equivalently: h @ Vh[:k].T @ Vh[:k]
        Pi_basis = Vh[:k].T  # (D, k)
        
        # Compute Pi(h): project h onto top-k subspace
        h_coarse_coords = hidden_states @ Pi_basis  # (B, k)
        h_coarse = h_coarse_coords @ Pi_basis.T     # (B, D) - back to original space
        
        # g(h): apply output layer to full hidden states
        g_h = model.get_output_from_hidden(hidden_states)  # (B, output_dim)
        
        # g(Pi(h)): apply output layer to projected hidden states
        g_Pi_h = model.get_output_from_hidden(h_coarse)    # (B, output_dim)
        
        # Pi(g(h)): project output of g(h) - but this doesn't make sense for logits
        # Instead, we measure how much g(h) differs from g(Pi(h))
        # This is the "closure error": how much does the tail affect the output?
        
        # Closure defect: ||g(h) - g(Pi(h))|| / ||g(h)||
        diff = g_h - g_Pi_h
        diff_norm = torch.norm(diff, dim=-1).mean()
        g_h_norm = torch.norm(g_h, dim=-1).mean() + 1e-10
        
        closure_defect = (diff_norm / g_h_norm).item()
        
        if return_components:
            # Also compute tail energy for comparison
            h_tail = hidden_states - h_coarse
            tail_energy = (h_tail ** 2).sum().item()
            total_energy = (hidden_states ** 2).sum().item()
            tail_defect = math.sqrt(tail_energy / (total_energy + 1e-10))
            
            return {
                'closure_defect': closure_defect,
                'tail_defect': tail_defect,
                'k': k,
                'diff_norm': diff_norm.item(),
                'g_h_norm': g_h_norm.item(),
            }
        
        return closure_defect


# ═══════════════════════════════════════════════════════════════════════════════
# TSALLIS ENTROPY AND Q-DIVERGENCE
# ═══════════════════════════════════════════════════════════════════════════════

def compute_tsallis_entropy(probs: torch.Tensor, q: float = 1.5) -> float:
    """
    Compute Tsallis entropy S_q(p) = (1 - sum(p_i^q)) / (q - 1)
    
    - q = 1: reduces to Shannon entropy (in the limit)
    - q > 1: emphasizes dominant probabilities (sub-additive)
    - q < 1: emphasizes rare events (super-additive)
    
    Args:
        probs: Probability distribution (sums to 1)
        q: Tsallis parameter (entropic index)
    
    Returns:
        Tsallis entropy value
    """
    probs = probs.clamp(min=1e-10)  # Avoid log(0)
    
    if abs(q - 1.0) < 1e-6:
        # Limit as q -> 1: Shannon entropy
        return -(probs * torch.log(probs)).sum().item()
    else:
        return ((1 - (probs ** q).sum()) / (q - 1)).item()


def compute_tsallis_entropy_normalized(probs: torch.Tensor, q: float = 1.5) -> float:
    """
    Compute normalized Tsallis entropy in [0, 1].
    
    Normalized by S_q(uniform), so 1 = maximum uncertainty.
    """
    n = probs.shape[-1]
    S_q = compute_tsallis_entropy(probs, q)
    
    # S_q(uniform) = (1 - n * (1/n)^q) / (q - 1) = (1 - n^(1-q)) / (q - 1)
    if abs(q - 1.0) < 1e-6:
        S_q_max = math.log(n)
    else:
        S_q_max = (1 - n ** (1 - q)) / (q - 1)
    
    return S_q / (S_q_max + 1e-10)


def compute_tsallis_divergence(p: torch.Tensor, r: torch.Tensor, q: float = 1.5) -> float:
    """
    Compute Tsallis relative entropy (q-divergence) D_q(p || r).
    
    D_q(p || r) = (1 - sum(p_i * (r_i/p_i)^(1-q))) / (q - 1)
                = (sum(p_i^q * r_i^(1-q)) - 1) / (q - 1)
    
    This is non-symmetric and non-negative, like KL divergence.
    
    Args:
        p: First distribution
        r: Second distribution (reference)
        q: Tsallis parameter
    
    Returns:
        Tsallis divergence value
    """
    p = p.clamp(min=1e-10)
    r = r.clamp(min=1e-10)
    
    if abs(q - 1.0) < 1e-6:
        # Limit as q -> 1: KL divergence
        return (p * torch.log(p / r)).sum().item()
    else:
        return (((p ** q) * (r ** (1 - q))).sum() - 1) / (q - 1)


def q_log(x: torch.Tensor, q: float) -> torch.Tensor:
    """q-logarithm: ln_q(x) = (x^(1-q) - 1) / (1 - q)"""
    if abs(q - 1.0) < 1e-6:
        return torch.log(x)
    return (x ** (1 - q) - 1) / (1 - q)


def q_exp(x: torch.Tensor, q: float) -> torch.Tensor:
    """q-exponential: exp_q(x) = [1 + (1-q)*x]_+^(1/(1-q))"""
    if abs(q - 1.0) < 1e-6:
        return torch.exp(x)
    base = 1 + (1 - q) * x
    return torch.relu(base) ** (1 / (1 - q))


# ═══════════════════════════════════════════════════════════════════════════════
# TEST
# ═══════════════════════════════════════════════════════════════════════════════

def test_analog_dataset():
    """Test the analog modular arithmetic dataset."""
    print("=" * 70)
    print("Testing Analog Modular Arithmetic Dataset")
    print("=" * 70)
    
    # Test configurations
    configs = [
        ("Discrete (baseline)", AnalogModularConfig(input_noise_std=0.0)),
        ("Noisy floats", AnalogModularConfig(input_noise_std=0.1)),
        ("Phase encoding", AnalogModularConfig(use_phase_encoding=True, phase_noise_std=0.05)),
        ("Soft targets", AnalogModularConfig(input_noise_std=0.1, use_soft_targets=True, target_concentration=10.0)),
    ]
    
    for name, config in configs:
        print(f"\n{name}:")
        dataset = AnalogModularDataset(config, split='train')
        x, y = dataset[0]
        print(f"  Input shape: {x.shape}, dtype: {x.dtype}")
        print(f"  Target shape: {y.shape if hasattr(y, 'shape') else 'scalar'}, dtype: {y.dtype}")
        print(f"  Sample input: {x.numpy()}")
        if hasattr(y, 'shape') and len(y.shape) > 0:
            print(f"  Target (soft): peak at {y.argmax().item()}, max={y.max():.3f}")
        else:
            print(f"  Target (hard): {y.item()}")


def test_tsallis():
    """Test Tsallis entropy computations."""
    print("\n" + "=" * 70)
    print("Testing Tsallis Entropy")
    print("=" * 70)
    
    # Uniform distribution
    p_uniform = torch.ones(10) / 10
    
    # Peaked distribution
    p_peaked = torch.zeros(10)
    p_peaked[0] = 0.9
    p_peaked[1:] = 0.1 / 9
    
    print("\nUniform distribution:")
    for q in [0.5, 1.0, 1.5, 2.0]:
        S_q = compute_tsallis_entropy(p_uniform, q)
        S_q_norm = compute_tsallis_entropy_normalized(p_uniform, q)
        print(f"  q={q}: S_q={S_q:.4f}, normalized={S_q_norm:.4f}")
    
    print("\nPeaked distribution (90% on one class):")
    for q in [0.5, 1.0, 1.5, 2.0]:
        S_q = compute_tsallis_entropy(p_peaked, q)
        S_q_norm = compute_tsallis_entropy_normalized(p_peaked, q)
        print(f"  q={q}: S_q={S_q:.4f}, normalized={S_q_norm:.4f}")
    
    print("\nTsallis divergence D_q(peaked || uniform):")
    for q in [0.5, 1.0, 1.5, 2.0]:
        D_q = compute_tsallis_divergence(p_peaked, p_uniform, q)
        print(f"  q={q}: D_q={D_q:.4f}")


def test_closure_defect():
    """Test layerwise closure defect computation."""
    print("\n" + "=" * 70)
    print("Testing Layerwise Closure Defect")
    print("=" * 70)
    
    # Create a simple model
    model = AnalogGrokMLP(input_dim=2, hidden_dim=64, output_dim=97, num_layers=2)
    
    # Generate some random hidden states
    torch.manual_seed(42)
    h = torch.randn(100, 64)
    
    # Compute closure defect
    result = compute_layerwise_closure_defect(model, h, return_components=True)
    
    print(f"\nClosure defect: {result['closure_defect']:.4f}")
    print(f"Tail defect:    {result['tail_defect']:.4f}")
    print(f"k (auto):       {result['k']}")
    print(f"||g(h) - g(Pi h)||: {result['diff_norm']:.4f}")
    print(f"||g(h)||:          {result['g_h_norm']:.4f}")
    
    print("\nNote: At random init, closure defect should be HIGH")
    print("After grokking, closure defect should be LOW (blanket closed)")


if __name__ == "__main__":
    test_analog_dataset()
    test_tsallis()
    test_closure_defect()
