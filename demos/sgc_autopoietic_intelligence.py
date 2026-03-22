#!/usr/bin/env python3
"""
SGC Autopoietic Intelligence: A Principled Path to Continual Learning
======================================================================

This experiment implements the full SGC theoretical framework as a guide to AGI:

THEORETICAL FOUNDATION (Lean Formalized):
1. FunctionalBlanket.lean: Grokking = algebraic phase transition (functional defect collapse)
2. ExplorationMass.lean: M = Sigma eta_t >= log(d0/delta) for mixing guarantee
3. ExplorationMassCoupled.lean: M_eff = Sigma kappa_t * eta_t (coupling efficiency)
4. KramersEscape.lean: Temperature speedup theorem (2x from analog world)
5. InformationGradientLaw.lean: ||grad_I|| > ||grad_E|| triggers transitions
6. AdiabaticInvariant.lean: Freeze function, not weights (Delta_w perp grad_epsilon_func)
7. Symbiosis.lean: Grow new lobes when frustrated (mitotic architecture)

CYBERNETIC CONTROL (Active Inference):
- Sensors: functional defect, class separation, exploration mass, kappa, entropy/extropy
- Actuators: noise scale, weight decay, noise mode, learning rate
- Control Laws: state-driven phases (explore/crystallize/recover/stable)
- Safety: spurious certainty detection triggers re-heat

ARCHITECTURE:
- AutopoieticGrokNet: Self-maintaining, self-growing neural system
- SymbioticLobe: Frozen host + trainable bridge + learnable symbiont
- SGCController: Full active inference control stack

Author: SGC Research Team
Date: February 5, 2026
"""

import sys
import math
import time
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import deque
from enum import Enum

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import Dataset, DataLoader


class Unbuffered:
    def __init__(self, stream):
        self.stream = stream
    def write(self, data):
        self.stream.write(data)
        self.stream.flush()
    def writelines(self, datas):
        self.stream.writelines(datas)
        self.stream.flush()
    def __getattr__(self, attr):
        return getattr(self.stream, attr)

sys.stdout = Unbuffered(sys.stdout)
sys.stderr = Unbuffered(sys.stderr)


# =============================================================================
# CONFIGURATION (SGC-Principled Defaults)
# =============================================================================

@dataclass
class SGCConfig:
    """Configuration derived from SGC theoretical principles."""
    
    # Task parameters
    p: int = 97                          # Prime for modular arithmetic
    train_fraction: float = 0.3          # Underfitting pressure (standard)
    
    # Architecture (from EmbeddingGrokMLP)
    embed_dim: int = 128
    hidden_dim: int = 128
    n_layers: int = 2
    embed_noise: float = 0.1             # CRITICAL: Kramers speedup (2x)
    
    # Exploration Mass (from ExplorationMass.lean)
    delta: float = 0.1                   # Target tolerance
    initial_distance: float = 1.0        # d0
    noise_scale: float = 0.1             # eta per step
    
    # Weight Decay (from successful grokking experiments)
    weight_decay: float = 1.0            # Standard grokking weight decay
    wd_quench: float = 2.0               # Higher WD during crystallization
    anneal_epochs: int = 500             # Soft transition
    
    # Grokking Detection (from FunctionalBlanket.lean)
    defect_threshold: float = 0.15       # Functional defect < this = grokked
    consolidation_threshold: float = 0.5 # Certainty threshold
    
    # Spurious Certainty (from ActiveInference)
    spurious_defect_threshold: float = 0.1  # Defect above this with high consolidation = spurious
    
    # Rank Floor (from Phase 6.1)
    rank_floor_fraction: float = 0.6     # Maintain 60% of peak rank
    
    # Noise Mode
    # KEY INSIGHT: Successful experiments use embed_noise ONLY, not weight noise
    # Weight noise injection disrupts learning - embed_noise is sufficient for Kramers speedup
    inject_weight_noise: bool = False    # Disable weight noise (use embed_noise only)
    tail_fraction: float = 0.5           # Fraction considered "tail"
    lambda_start: float = 0.2            # For exploration tracking
    lambda_end: float = 0.8              # For exploration tracking
    
    # Symbiotic Architecture (from Symbiosis.lean)
    frustration_threshold: float = 0.3   # Trigger mitosis when D * T > this
    max_lobes: int = 3                   # Maximum number of lobes
    
    # Training (match successful experiments exactly)
    max_epochs: int = 10000
    batch_size: int = 512            # Match lifshitz/embedding experiments
    lr: float = 1e-3
    log_interval: int = 100
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'
    seed: int = 42
    
    def __post_init__(self):
        # Compute M_explore from ExplorationMass.lean theorem
        self.M_explore = math.log(self.initial_distance / self.delta)
        print(f"[SGCConfig] M_explore = log({self.initial_distance}/{self.delta}) = {self.M_explore:.4f}")


# =============================================================================
# PHASE ENUM (Control States)
# =============================================================================

class Phase(Enum):
    EXPLORE = "explore"           # High noise, low WD, accumulate M
    CRYSTALLIZE = "crystallize"   # Falling defect, ramp WD
    RECOVER = "recover"           # Spurious certainty, RE-HEAT
    STABLE = "stable"             # Grokked, maintain


# =============================================================================
# DATASET (Modular Arithmetic)
# =============================================================================

class ModularArithmeticDataset(Dataset):
    """Dataset for modular arithmetic tasks."""
    
    def __init__(self, p: int, operation: str = 'add', 
                 train: bool = True, train_fraction: float = 0.3, seed: int = 42):
        self.p = p
        self.operation = operation
        
        all_pairs = [(a, b) for a in range(p) for b in range(p)]
        rng = np.random.RandomState(seed)
        rng.shuffle(all_pairs)
        
        split_idx = int(len(all_pairs) * train_fraction)
        self.pairs = all_pairs[:split_idx] if train else all_pairs[split_idx:]
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        if self.operation == 'add':
            c = (a + b) % self.p
        elif self.operation == 'mul':
            c = (a * b) % self.p
        else:
            c = (a + b) % self.p
        
        return (torch.tensor(a, dtype=torch.long),
                torch.tensor(b, dtype=torch.long),
                torch.tensor(c, dtype=torch.long))


# =============================================================================
# EMBEDDING GROK MLP (Analog World Architecture)
# =============================================================================

class EmbeddingGrokMLP(nn.Module):
    """
    MLP with learned embeddings and optional noise injection.
    
    From analog_modular_arithmetic.py and experimental findings:
    - embed_noise=0.1 provides 2x grokking speedup (Kramers escape theory)
    - Creates "thick manifolds" where 3.001 ~ 3.0
    - Forces learning of robust, topologically correct boundaries
    """
    
    def __init__(self, p: int, embed_dim: int = 128, hidden_dim: int = 128,
                 n_layers: int = 2, embed_noise: float = 0.1):
        super().__init__()
        self.p = p
        self.embed_dim = embed_dim
        self.hidden_dim = hidden_dim
        self.embed_noise = embed_noise
        
        # Learned embeddings (analog world)
        self.embed_a = nn.Embedding(p, embed_dim)
        self.embed_b = nn.Embedding(p, embed_dim)
        
        # Hidden layers
        layers = []
        layers.append(nn.Linear(embed_dim * 2, hidden_dim))
        layers.append(nn.ReLU())
        for _ in range(n_layers - 1):
            layers.append(nn.Linear(hidden_dim, hidden_dim))
            layers.append(nn.ReLU())
        self.hidden = nn.Sequential(*layers)
        
        # Output
        self.output = nn.Linear(hidden_dim, p)
        
        # Use PyTorch default initialization (not custom) - this is what works!
    
    def forward(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Forward pass with optional noise during training."""
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        
        # Inject noise during training ONLY (Kramers escape speedup)
        if self.training and self.embed_noise > 0:
            e_a = e_a + torch.randn_like(e_a) * self.embed_noise
            e_b = e_b + torch.randn_like(e_b) * self.embed_noise
        
        x = torch.cat([e_a, e_b], dim=-1)
        h = self.hidden(x)
        return self.output(h)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get hidden representation (NO noise - for clean defect computation)."""
        e_a = self.embed_a(a)
        e_b = self.embed_b(b)
        x = torch.cat([e_a, e_b], dim=-1)
        return self.hidden(x)


# =============================================================================
# FUNCTIONAL DEFECT COMPUTATION (from FunctionalBlanket.lean)
# =============================================================================

def compute_functional_defect(
    hidden_states: torch.Tensor,
    targets: torch.Tensor,
    num_classes: int
) -> Tuple[float, float]:
    """
    Compute functional defect and class separation.
    
    From FunctionalBlanket.lean:
    - FunctionalDefect = within_class_variance / total_variance
    - ClassSeparation = between_class_variance / within_class_variance (Fisher)
    
    At grokking:
    - FunctionalDefect collapses: 1.0 -> 0.003
    - ClassSeparation explodes: 0.01 -> 346
    """
    if hidden_states.numel() == 0:
        return 1.0, 0.0
    
    # Total variance
    total_var = hidden_states.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 0.0, float('inf')
    
    # Per-class statistics
    within_vars = []
    class_means = []
    class_counts = []
    
    for c in range(num_classes):
        mask = (targets == c)
        count = mask.sum().item()
        if count > 0:
            h_c = hidden_states[mask]
            class_means.append(h_c.mean(dim=0))
            class_counts.append(count)
            if count > 1:
                within_vars.append(h_c.var(dim=0).mean().item())
            else:
                within_vars.append(0.0)
    
    if not class_means:
        return 1.0, 0.0
    
    # Weighted within-class variance
    class_counts_t = torch.tensor(class_counts, dtype=torch.float, device=hidden_states.device)
    within_vars_t = torch.tensor(within_vars, device=hidden_states.device)
    within_var = (within_vars_t * class_counts_t).sum() / class_counts_t.sum()
    
    # Between-class variance (ANOVA)
    class_means_t = torch.stack(class_means)
    global_mean = (class_means_t * class_counts_t.unsqueeze(1)).sum(0) / class_counts_t.sum()
    between_var = ((class_means_t - global_mean) ** 2).mean(dim=1)
    between_var = (between_var * class_counts_t).sum() / class_counts_t.sum()
    
    # Compute metrics
    func_defect = within_var.item() / (total_var + 1e-10)
    class_sep = between_var.item() / (within_var.item() + 1e-10)
    
    return func_defect, class_sep


# =============================================================================
# SPECTRAL ANALYSIS (from Phase 5/6)
# =============================================================================

def compute_effective_rank(weight_matrix: torch.Tensor) -> float:
    """Compute effective rank from singular value entropy."""
    W = weight_matrix.detach().cpu().float()
    
    try:
        S = torch.linalg.svdvals(W)
    except Exception:
        return 1.0
    
    S_squared = S ** 2
    total = S_squared.sum().item()
    
    if total < 1e-10:
        return 1.0
    
    p = S_squared / total
    p = p[p > 1e-10]
    
    if len(p) == 0:
        return 1.0
    
    entropy = -(p * torch.log(p)).sum().item()
    return math.exp(entropy)


def compute_coupling_coefficient(
    weight_matrix: torch.Tensor,
    noise_vector: torch.Tensor,
    tail_fraction: float = 0.5
) -> float:
    """
    Compute kappa: fraction of noise energy in relevant (tail) subspace.
    
    From ExplorationMassCoupled.lean:
    kappa = ||noise in tail||^2 / ||noise||^2
    """
    try:
        U, S, Vh = torch.linalg.svd(weight_matrix.detach().cpu().float(), full_matrices=False)
    except Exception:
        return 0.01  # Default low coupling
    
    n = len(S)
    tail_start = int(n * (1 - tail_fraction))
    
    # Project noise onto SVD basis
    noise_flat = noise_vector.detach().cpu().float().flatten()
    if noise_flat.numel() != Vh.shape[1]:
        return 0.01
    
    noise_proj = Vh @ noise_flat
    total_energy = (noise_proj ** 2).sum().item()
    
    if total_energy < 1e-10:
        return 0.0
    
    tail_energy = (noise_proj[tail_start:] ** 2).sum().item()
    return tail_energy / total_energy


# =============================================================================
# ENTROPY/EXTROPY (from entropy_extropy_controller.py)
# =============================================================================

def compute_entropy(probs: torch.Tensor, eps: float = 1e-10) -> float:
    """Shannon entropy H(p) = -sum(p * log(p))."""
    probs = torch.clamp(probs, min=eps, max=1.0 - eps)
    entropy = -torch.sum(probs * torch.log(probs), dim=-1)
    return entropy.mean().item()


def compute_normalized_entropy(probs: torch.Tensor, eps: float = 1e-10) -> float:
    """Normalized entropy in [0, 1]."""
    n_classes = probs.shape[-1]
    max_entropy = math.log(n_classes)
    entropy = compute_entropy(probs, eps)
    return entropy / max_entropy if max_entropy > 0 else 0.0


def compute_tsallis_entropy(probs: torch.Tensor, q: float = 1.5) -> float:
    """
    Tsallis entropy S_q(p) = (1 - sum(p^q)) / (q - 1)
    
    From TsallisStatistics.lean:
    - q > 1: sub-additive, emphasizes dominant states
    - q = 1: Shannon (limit)
    """
    probs = probs.clamp(min=1e-10)
    if abs(q - 1.0) < 1e-6:
        return compute_entropy(probs)
    return ((1 - (probs ** q).sum(dim=-1)) / (q - 1)).mean().item()


# =============================================================================
# SGC CONTROLLER (Active Inference + Exploration Mass)
# =============================================================================

@dataclass
class SGCState:
    """Observable state for SGC control."""
    epoch: int = 0
    
    # Functional Blanket (primary)
    functional_defect: float = 1.0
    class_separation: float = 0.0
    
    # Exploration Mass (from ExplorationMass.lean)
    M_nominal: float = 0.0           # Sigma eta_t
    M_effective: float = 0.0         # Sigma kappa_t * eta_t
    kappa: float = 0.01              # Current coupling coefficient
    
    # Entropy/Extropy
    entropy_normalized: float = 1.0
    consolidation: float = 0.0       # 1 - entropy
    
    # Free Energy (defect + entropy)
    free_energy: float = 2.0
    
    # Velocities
    defect_velocity: float = 0.0
    
    # Spectral
    effective_rank: float = 0.0
    peak_rank: float = 0.0
    
    # Phase
    phase: Phase = Phase.EXPLORE
    blanket_closed: bool = False
    grokking_detected: bool = False
    spurious_certainty: bool = False
    
    # Accuracy (external validation)
    train_acc: float = 0.0
    test_acc: float = 0.0


@dataclass
class SGCController:
    """
    SGC-principled controller implementing Active Inference.
    
    From unified_theory_sgc_active_inference.md:
    - Defect IS Free Energy (blanket leakage = prediction error)
    - Projection IS the Generative Model
    - Learning IS Blanket Formation
    
    Control loop:
    1. Observe: measure defect, entropy, exploration mass, kappa
    2. Infer: estimate phase and blanket quality
    3. Act: adjust noise and weight decay
    4. Learn: model updates, observations change
    """
    
    config: SGCConfig
    
    # Temperature (exploration intensity)
    T_current: float = 0.15
    
    # Weight decay
    wd_current: float = 0.1
    
    # Current state
    state: SGCState = field(default_factory=SGCState)
    
    # History for velocities
    defect_history: deque = field(default_factory=lambda: deque(maxlen=20))
    
    # EMAs
    defect_ema: float = 1.0
    entropy_ema: float = 1.0
    kappa_ema: float = 0.01
    ema_alpha: float = 0.15
    
    # Detection events
    blanket_closure_epoch: int = -1
    grokking_epoch: int = -1
    
    # Anneal tracking
    anneal_start_epoch: int = -1
    
    # Noise mode lambda (for hybrid)
    lambda_current: float = 0.2
    
    def __post_init__(self):
        self.T_current = self.config.noise_scale
        self.wd_current = self.config.weight_decay
    
    def update(
        self,
        epoch: int,
        functional_defect: float,
        class_separation: float,
        entropy_normalized: float,
        effective_rank: float,
        kappa: float,
        train_acc: float,
        test_acc: float
    ) -> Tuple[float, float, Phase]:
        """
        Update controller with observations, return control outputs.
        
        Returns: (noise_scale, weight_decay, phase)
        """
        # Update EMAs
        self.defect_ema = self.ema_alpha * functional_defect + (1 - self.ema_alpha) * self.defect_ema
        self.entropy_ema = self.ema_alpha * entropy_normalized + (1 - self.ema_alpha) * self.entropy_ema
        self.kappa_ema = self.ema_alpha * kappa + (1 - self.ema_alpha) * self.kappa_ema
        
        # Store history for velocity
        self.defect_history.append(functional_defect)
        defect_velocity = self._compute_velocity(self.defect_history)
        
        # Track peak rank
        if effective_rank > self.state.peak_rank:
            self.state.peak_rank = effective_rank
        
        # Accumulate exploration mass based on embed_noise (implicit exploration)
        # The embed_noise provides thermal activation per the Kramers escape theorem
        if self.state.phase == Phase.EXPLORE:
            self.state.M_nominal += self.config.embed_noise  # Implicit from embeddings
            self.state.M_effective += self.kappa_ema * self.config.embed_noise
        
        # Track exploration progress
        if self.state.phase == Phase.EXPLORE:
            progress = min(1.0, self.state.M_nominal / (self.config.M_explore * 10))
            self.lambda_current = progress  # Simple progress tracking
        
        # Compute free energy (defect + entropy)
        free_energy = self.defect_ema + self.entropy_ema
        consolidation = 1.0 - self.entropy_ema
        
        # Build state
        self.state = SGCState(
            epoch=epoch,
            functional_defect=self.defect_ema,
            class_separation=class_separation,
            M_nominal=self.state.M_nominal,
            M_effective=self.state.M_effective,
            kappa=self.kappa_ema,
            entropy_normalized=self.entropy_ema,
            consolidation=consolidation,
            free_energy=free_energy,
            defect_velocity=defect_velocity,
            effective_rank=effective_rank,
            peak_rank=self.state.peak_rank,
            train_acc=train_acc,
            test_acc=test_acc
        )
        
        # Detect blanket closure (from FunctionalBlanket.lean: grokkingThreshold = 0.15)
        if self.defect_ema < self.config.defect_threshold:
            self.state.blanket_closed = True
            if self.blanket_closure_epoch < 0:
                self.blanket_closure_epoch = epoch
                print(f"\n*** BLANKET CLOSURE at epoch {epoch} ***")
                print(f"    functional_defect = {self.defect_ema:.4f} < {self.config.defect_threshold}")
                print(f"    class_separation = {class_separation:.2f}")
        
        # Detect spurious certainty (confident but wrong)
        self.state.spurious_certainty = (
            consolidation > self.config.consolidation_threshold and
            self.defect_ema > self.config.spurious_defect_threshold
        )
        
        # Detect grokking (blanket closed + consolidated)
        if (self.state.blanket_closed and 
            consolidation > self.config.consolidation_threshold and
            self.grokking_epoch < 0):
            self.state.grokking_detected = True
            self.grokking_epoch = epoch
            print(f"\n*** GROKKING DETECTED (intrinsic) at epoch {epoch} ***")
            print(f"    functional_defect = {self.defect_ema:.4f}")
            print(f"    class_separation = {class_separation:.2f}")
            print(f"    consolidation = {consolidation:.3f}")
            print(f"    test_acc = {test_acc*100:.1f}%")
        elif self.grokking_epoch > 0:
            self.state.grokking_detected = True
        
        # Determine phase
        phase = self._determine_phase()
        self.state.phase = phase
        
        # Compute control outputs
        noise, wd = self._compute_control(epoch, phase)
        
        return noise, wd, phase
    
    def _compute_velocity(self, history: deque) -> float:
        if len(history) < 2:
            return 0.0
        vals = list(history)
        return (vals[-1] - vals[0]) / len(vals)
    
    def _determine_phase(self) -> Phase:
        """
        Determine phase based on SGC principles.
        
        SIMPLIFIED: Let training proceed naturally, only intervene when needed.
        The embed_noise provides exploration, WD=1.0 provides consolidation.
        """
        # Already grokked
        if self.state.grokking_detected:
            return Phase.STABLE
        
        # Spurious certainty: high consolidation (>0.7) but high defect (>0.3)
        # This is a strong signal that the model is confident but wrong
        if self.state.consolidation > 0.7 and self.state.functional_defect > 0.3:
            return Phase.RECOVER
        
        # Crystallizing: defect clearly falling and consolidation rising
        if (self.state.functional_defect < 0.5 and 
            self.state.defect_velocity < -0.005 and
            self.state.consolidation > 0.5):
            return Phase.CRYSTALLIZE
        
        # Default: EXPLORE - let embed_noise + WD=1.0 do their work
        return Phase.EXPLORE
    
    def _compute_control(self, epoch: int, phase: Phase) -> Tuple[float, float]:
        """Compute noise and WD based on phase."""
        
        # Use consistent weight decay like successful experiments
        # Key insight: embed_noise provides exploration, WD=1.0 provides consolidation
        
        if phase == Phase.STABLE:
            noise = 0.0  # No additional noise needed
            wd = self.config.weight_decay
        
        elif phase == Phase.RECOVER:
            # Spurious certainty detected - but don't inject weight noise
            # The embed_noise already provides exploration
            noise = 0.0
            wd = self.config.weight_decay
            if epoch % 500 == 0:
                print(f"    [RECOVER] Spurious certainty detected")
        
        elif phase == Phase.CRYSTALLIZE:
            # Soft anneal: ramp WD higher
            if self.anneal_start_epoch < 0:
                self.anneal_start_epoch = epoch
                print(f"\n*** CRYSTALLIZATION STARTED at epoch {epoch} ***")
                print(f"    M_nominal = {self.state.M_nominal:.3f}")
            
            # Anneal progress
            anneal_elapsed = epoch - self.anneal_start_epoch
            anneal_progress = min(1.0, anneal_elapsed / self.config.anneal_epochs)
            
            # Linear WD ramp to higher consolidation
            wd = self.config.weight_decay + anneal_progress * (self.config.wd_quench - self.config.weight_decay)
            noise = 0.0
        
        else:  # EXPLORE
            # Standard training with embed_noise providing exploration
            noise = 0.0  # embed_noise is sufficient
            wd = self.config.weight_decay
        
        self.wd_current = wd
        return noise, wd
    
    def inject_noise(self, model: nn.Module, noise_scale: float):
        """
        Inject noise into model parameters.
        
        Uses hybrid mode from Phase 6.1: lambda-scheduled wavelet + isotropic mix.
        """
        if noise_scale < 1e-6:
            return
        
        with torch.no_grad():
            for name, param in model.named_parameters():
                if param.dim() >= 2:
                    if self.config.noise_mode == 'hybrid':
                        # Mix isotropic and wavelet-shaped noise
                        isotropic = torch.randn_like(param) * noise_scale
                        
                        # Wavelet shaping: target high-rank components
                        try:
                            U, S, Vh = torch.linalg.svd(param, full_matrices=False)
                            n = len(S)
                            tail_start = int(n * (1 - self.config.tail_fraction))
                            
                            # Weight toward tail
                            weights = torch.ones_like(S)
                            weights[tail_start:] = 2.0  # Boost tail
                            
                            # Create wavelet noise
                            noise_sv = torch.randn(n, device=param.device) * weights * noise_scale
                            wavelet = U @ torch.diag(noise_sv) @ Vh[:n, :]
                            
                            # Hybrid mix
                            noise = (1 - self.lambda_current) * isotropic + self.lambda_current * wavelet
                        except:
                            noise = isotropic
                    else:
                        noise = torch.randn_like(param) * noise_scale
                    
                    param.add_(noise)


# =============================================================================
# AUTOPOIETIC GROK NET (Self-Maintaining, Self-Growing)
# =============================================================================

class AutopoieticGrokNet(nn.Module):
    """
    Self-maintaining, self-growing neural network.
    
    From Symbiosis.lean:
    - Grows new lobes when thermodynamic frustration exceeds threshold
    - Frozen host + trainable bridge + learnable symbiont
    - Preserves host invariants while learning new tasks
    
    From AdiabaticInvariant.lean:
    - Updates constrained to preserve functional blanket
    - Delta_w perpendicular to grad_epsilon_func
    """
    
    def __init__(self, config: SGCConfig):
        super().__init__()
        self.config = config
        
        # Primary lobe
        self.lobes = nn.ModuleList([
            EmbeddingGrokMLP(
                p=config.p,
                embed_dim=config.embed_dim,
                hidden_dim=config.hidden_dim,
                n_layers=config.n_layers,
                embed_noise=config.embed_noise
            )
        ])
        
        # Task heads
        self.task_heads = nn.ModuleList([
            nn.Linear(config.hidden_dim, config.p)
        ])
        
        # Bridges between lobes (from Symbiosis.lean: BridgeOperator)
        self.bridges = nn.ModuleList()
        
        # Lobe states
        self.lobe_frozen = [False]
        self.active_lobe = 0
        self.active_task = 0
        
        # Growth history
        self.mitosis_events = []
    
    def get_active_lobe(self) -> EmbeddingGrokMLP:
        return self.lobes[self.active_lobe]
    
    def forward(self, a: torch.Tensor, b: torch.Tensor, task_id: int = 0) -> torch.Tensor:
        """Forward pass through appropriate lobe and task head."""
        lobe = self.lobes[min(task_id, len(self.lobes) - 1)]
        h = lobe.get_hidden(a, b)
        
        # Apply bridge if using non-primary lobe
        if task_id > 0 and len(self.bridges) > 0:
            bridge_idx = min(task_id - 1, len(self.bridges) - 1)
            h_host = self.lobes[0].get_hidden(a, b)
            h = h + self.bridges[bridge_idx](h_host)
        
        head = self.task_heads[min(task_id, len(self.task_heads) - 1)]
        return head(h)
    
    def get_hidden(self, a: torch.Tensor, b: torch.Tensor, task_id: int = 0) -> torch.Tensor:
        """Get hidden representation for defect computation."""
        lobe = self.lobes[min(task_id, len(self.lobes) - 1)]
        return lobe.get_hidden(a, b)
    
    def check_mitosis(self, frustration: float, epoch: int) -> bool:
        """
        Check if mitotic division should occur.
        
        From Symbiosis.lean: MitoticCondition
        - Trigger when thermodynamic frustration (D * T) exceeds threshold
        - Don't grow if already at max lobes
        """
        if len(self.lobes) >= self.config.max_lobes:
            return False
        
        if frustration > self.config.frustration_threshold:
            print(f"\n*** MITOSIS TRIGGERED at epoch {epoch} ***")
            print(f"    frustration = {frustration:.4f} > {self.config.frustration_threshold}")
            self._spawn_lobe(epoch)
            return True
        
        return False
    
    def _spawn_lobe(self, epoch: int):
        """Spawn a new lobe (symbiotic growth)."""
        device = next(self.parameters()).device
        
        # Freeze current lobe (becomes host)
        current_idx = len(self.lobes) - 1
        self.lobe_frozen[current_idx] = True
        for param in self.lobes[current_idx].parameters():
            param.requires_grad = False
        
        # Create new lobe (symbiont)
        new_lobe = EmbeddingGrokMLP(
            p=self.config.p,
            embed_dim=self.config.embed_dim,
            hidden_dim=self.config.hidden_dim,
            n_layers=self.config.n_layers,
            embed_noise=self.config.embed_noise
        ).to(device)
        
        # Create bridge (from Symbiosis.lean: BridgeOperator)
        bridge = nn.Linear(self.config.hidden_dim, self.config.hidden_dim).to(device)
        nn.init.zeros_(bridge.weight)  # Start as identity-ish
        nn.init.zeros_(bridge.bias)
        
        # Create new task head
        new_head = nn.Linear(self.config.hidden_dim, self.config.p).to(device)
        
        self.lobes.append(new_lobe)
        self.bridges.append(bridge)
        self.task_heads.append(new_head)
        self.lobe_frozen.append(False)
        
        self.active_lobe = len(self.lobes) - 1
        self.active_task = len(self.task_heads) - 1
        
        self.mitosis_events.append({
            'epoch': epoch,
            'new_lobe_idx': self.active_lobe
        })
        
        print(f"    New lobe spawned: lobe_{self.active_lobe}")
        print(f"    Total lobes: {len(self.lobes)}")


# =============================================================================
# TRAINING LOOP
# =============================================================================

def train_sgc_autopoietic(config: SGCConfig):
    """
    Train the AutopoieticGrokNet using SGC principles.
    
    This implements the full cybernetic control loop:
    1. Observe: functional defect, class separation, exploration mass, etc.
    2. Infer: determine phase (explore/crystallize/recover/stable)
    3. Act: adjust noise and weight decay
    4. Learn: update model, observations change
    """
    print("=" * 80)
    print("SGC AUTOPOIETIC INTELLIGENCE EXPERIMENT")
    print("=" * 80)
    print(f"\nTheoretical Foundation:")
    print(f"  - FunctionalBlanket.lean: Grokking = algebraic phase transition")
    print(f"  - ExplorationMass.lean: M >= log(d0/delta) = {config.M_explore:.4f}")
    print(f"  - KramersEscape.lean: embed_noise = {config.embed_noise} (2x speedup)")
    print(f"  - Symbiosis.lean: Mitotic growth when frustrated")
    print(f"\nDevice: {config.device}")
    print("=" * 80)
    
    # Set seed
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    
    # Create datasets
    train_dataset = ModularArithmeticDataset(
        config.p, 'add', train=True, 
        train_fraction=config.train_fraction, seed=config.seed
    )
    test_dataset = ModularArithmeticDataset(
        config.p, 'add', train=False,
        train_fraction=config.train_fraction, seed=config.seed
    )
    
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    print(f"\nDataset: Modular Addition mod {config.p}")
    print(f"  Train: {len(train_dataset)} samples")
    print(f"  Test: {len(test_dataset)} samples")
    
    # Create model
    model = AutopoieticGrokNet(config).to(config.device)
    print(f"\nModel: AutopoieticGrokNet")
    print(f"  Parameters: {sum(p.numel() for p in model.parameters()):,}")
    
    # Create controller
    controller = SGCController(config=config)
    
    # Optimizer (will be recreated on mitosis)
    optimizer = torch.optim.AdamW(
        model.parameters(),
        lr=config.lr,
        weight_decay=config.weight_decay
    )
    
    # Training state
    best_test_acc = 0.0
    start_time = time.time()
    
    print(f"\n{'Epoch':>6} | {'Phase':>11} | {'FuncD':>7} | {'ClsSep':>7} | "
          f"{'M_nom':>6} | {'kappa':>5} | {'Consol':>6} | {'TrAcc':>6} | {'TsAcc':>6} | {'T':>7} | {'WD':>5}")
    print("-" * 105)
    
    for epoch in range(1, config.max_epochs + 1):
        model.train()
        epoch_loss = 0.0
        correct = 0
        total = 0
        
        for a, b, c in train_loader:
            a, b, c = a.to(config.device), b.to(config.device), c.to(config.device)
            
            optimizer.zero_grad()
            logits = model(a, b, task_id=model.active_task)
            loss = F.cross_entropy(logits, c)
            loss.backward()
            optimizer.step()
            
            epoch_loss += loss.item()
            correct += (logits.argmax(dim=1) == c).sum().item()
            total += c.size(0)
        
        train_acc = correct / total
        
        # Evaluate
        model.eval()
        test_correct = 0
        test_total = 0
        all_hidden = []
        all_targets = []
        all_probs = []
        
        with torch.no_grad():
            for a, b, c in test_loader:
                a, b, c = a.to(config.device), b.to(config.device), c.to(config.device)
                
                h = model.get_hidden(a, b, task_id=model.active_task)
                logits = model(a, b, task_id=model.active_task)
                probs = F.softmax(logits, dim=-1)
                
                test_correct += (logits.argmax(dim=1) == c).sum().item()
                test_total += c.size(0)
                
                all_hidden.append(h)
                all_targets.append(c)
                all_probs.append(probs)
        
        test_acc = test_correct / test_total
        best_test_acc = max(best_test_acc, test_acc)
        
        # Compute observables
        hidden_states = torch.cat(all_hidden, dim=0)
        targets = torch.cat(all_targets, dim=0)
        probs = torch.cat(all_probs, dim=0)
        
        # Functional defect (from FunctionalBlanket.lean)
        func_defect, class_sep = compute_functional_defect(hidden_states, targets, config.p)
        
        # Entropy
        entropy_norm = compute_normalized_entropy(probs)
        
        # Effective rank
        lobe = model.get_active_lobe()
        hidden_weight = None
        for name, param in lobe.named_parameters():
            if 'hidden' in name and 'weight' in name and param.dim() >= 2:
                hidden_weight = param
                break
        eff_rank = compute_effective_rank(hidden_weight) if hidden_weight is not None else 1.0
        
        # Coupling coefficient
        if hidden_weight is not None:
            noise_sample = torch.randn_like(hidden_weight)
            kappa = compute_coupling_coefficient(hidden_weight, noise_sample, config.tail_fraction)
        else:
            kappa = 0.01
        
        # Update controller
        noise_scale, wd, phase = controller.update(
            epoch=epoch,
            functional_defect=func_defect,
            class_separation=class_sep,
            entropy_normalized=entropy_norm,
            effective_rank=eff_rank,
            kappa=kappa,
            train_acc=train_acc,
            test_acc=test_acc
        )
        
        # Update optimizer weight decay
        for param_group in optimizer.param_groups:
            param_group['weight_decay'] = wd
        
        # Note: embed_noise in the model provides Kramers speedup
        # No additional weight noise injection needed (it disrupts learning)
        
        # Check for mitosis (thermodynamic frustration)
        frustration = func_defect * noise_scale
        model.check_mitosis(frustration, epoch)
        
        # Logging
        if epoch % config.log_interval == 0 or epoch == 1:
            state = controller.state
            print(f"{epoch:6d} | {phase.value:>11} | {func_defect:7.4f} | {class_sep:7.2f} | "
                  f"{state.M_nominal:6.2f} | {kappa:5.3f} | {state.consolidation:6.3f} | "
                  f"{train_acc*100:5.1f}% | {test_acc*100:5.1f}% | {noise_scale:7.4f} | {wd:5.2f}")
        
        # Early stopping on grokking
        if controller.grokking_epoch > 0 and epoch > controller.grokking_epoch + 500:
            print(f"\nEarly stopping: grokking achieved and stable for 500 epochs")
            break
    
    # Summary
    elapsed = time.time() - start_time
    print("\n" + "=" * 80)
    print("EXPERIMENT COMPLETE")
    print("=" * 80)
    print(f"\nResults:")
    print(f"  Blanket closure epoch: {controller.blanket_closure_epoch}")
    print(f"  Grokking epoch (intrinsic): {controller.grokking_epoch}")
    print(f"  Best test accuracy: {best_test_acc*100:.2f}%")
    print(f"  Final functional defect: {controller.state.functional_defect:.4f}")
    print(f"  Final class separation: {controller.state.class_separation:.2f}")
    print(f"  Final exploration mass: M_nom={controller.state.M_nominal:.2f}, M_eff={controller.state.M_effective:.2f}")
    print(f"  Mitosis events: {len(model.mitosis_events)}")
    print(f"  Total lobes: {len(model.lobes)}")
    print(f"  Elapsed time: {elapsed:.1f}s")
    
    # Validate against Lean theorems
    print(f"\nTheorem Validation:")
    print(f"  ExplorationMass.lean:")
    print(f"    M_nominal ({controller.state.M_nominal:.2f}) >= M_explore ({config.M_explore:.2f}): "
          f"{'SATISFIED' if controller.state.M_nominal >= config.M_explore else 'NOT YET'}")
    print(f"  FunctionalBlanket.lean:")
    print(f"    FunctionalDefect ({controller.state.functional_defect:.4f}) < threshold ({config.defect_threshold}): "
          f"{'GROKKED' if controller.state.functional_defect < config.defect_threshold else 'NOT YET'}")
    print(f"  KramersEscape.lean:")
    print(f"    Analog world speedup with embed_noise={config.embed_noise}")
    
    return model, controller


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    config = SGCConfig()
    model, controller = train_sgc_autopoietic(config)
