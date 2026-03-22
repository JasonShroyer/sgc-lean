"""
Adaptive Polarity: Modular Arithmetic Validation

CRITICAL FALSIFICATION TEST:
- Sudoku learned g → 0 (Repulsion)
- Modular Arithmetic SHOULD learn g → 1 (Attraction)

If it learns g → 0 for arithmetic, our theory is wrong.

Task: x, y ∈ [0..9], z = (x + y) mod 10
Graph: x → z, y → z (Attractive constraints: cells should AGREE on z)
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass
from typing import List, Tuple, Dict, Optional
import numpy as np
from datetime import datetime
import os


@dataclass
class ArithmeticConfig:
    """Configuration for modular arithmetic test."""
    
    stalk_dim: int = 32
    num_cells: int = 3  # x, y, z
    num_digits: int = 10
    diffusion_steps: int = 8
    diffusion_dt: float = 0.1
    
    # Homeostatic
    tau: float = 0.3
    ema_alpha: float = 0.95
    
    # Langevin
    noise_scale: float = 0.3
    min_temp: float = 0.01
    
    # Polarity
    polarity_init: float = 0.0  # Start neutral
    
    # Training
    epochs: int = 300
    batch_size: int = 64
    lr: float = 1e-3
    polarity_lr: float = 0.05
    
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_arithmetic"


def generate_arithmetic_data(n_samples: int, seed: int = 42):
    """Generate modular arithmetic data: z = (x + y) mod 10."""
    np.random.seed(seed)
    
    x = np.random.randint(0, 10, size=n_samples)
    y = np.random.randint(0, 10, size=n_samples)
    z = (x + y) % 10
    
    # Format: [x, y, 0] for puzzle (z is unknown), z for solution
    puzzles = np.stack([x, y, np.zeros(n_samples, dtype=int)], axis=1)
    solutions = z
    
    return puzzles, solutions


def build_arithmetic_graph() -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
    """
    Build graph for x + y = z (mod 10).
    
    Edges: x → z, y → z
    Both edges should be ATTRACTIVE (output should agree with function of inputs).
    """
    edges = [(0, 2), (1, 2)]  # x→z, y→z
    edge_types = {'xy_to_z': [0, 1]}
    return edges, edge_types


class ArithmeticDiffusion(nn.Module):
    """Diffusion for arithmetic with learnable polarity."""
    
    def __init__(self, stalk_dim: int, num_digits: int,
                 edges: List[Tuple[int, int]],
                 polarity_init: float = 0.0,
                 noise_scale: float = 0.3):
        super().__init__()
        self.stalk_dim = stalk_dim
        self.num_digits = num_digits
        self.num_edges = len(edges)
        self.noise_scale = noise_scale
        
        src_indices = torch.tensor([e[0] for e in edges], dtype=torch.long)
        dst_indices = torch.tensor([e[1] for e in edges], dtype=torch.long)
        self.register_buffer('src_idx', src_indices)
        self.register_buffer('dst_idx', dst_indices)
        
        # Single polarity for all edges (simple case)
        self.polarity_logit = nn.Parameter(torch.tensor(polarity_init))
        
        # Restriction map (learned function from inputs to output)
        self.restriction = nn.Sequential(
            nn.Linear(stalk_dim, stalk_dim * 2),
            nn.GELU(),
            nn.Linear(stalk_dim * 2, stalk_dim),
        )
    
    def get_mixture_weight(self) -> torch.Tensor:
        return torch.sigmoid(self.polarity_logit)
    
    def compute_energies(self, logits: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor]:
        """Compute energies."""
        probs = F.softmax(logits, dim=-1)  # (batch, 3, 10)
        
        src_probs = probs[:, self.src_idx, :]  # (batch, 2, 10)
        dst_probs = probs[:, self.dst_idx, :]  # (batch, 2, 10) - both point to z
        
        # Attractive: ||p_src - p_dst||²
        attractive = ((src_probs - dst_probs) ** 2).sum(dim=-1).mean()
        
        # Repulsive: <p_src, p_dst>
        repulsive = (src_probs * dst_probs).sum(dim=-1).mean()
        
        g = self.get_mixture_weight()
        combined = g * attractive + (1 - g) * repulsive
        
        return combined, g
    
    def diffuse(self, stalks: torch.Tensor, logits: torch.Tensor,
                dt: float, clue_mask: torch.Tensor, temperature: torch.Tensor) -> torch.Tensor:
        """Langevin diffusion step."""
        batch_size = stalks.shape[0]
        
        probs = F.softmax(logits, dim=-1)
        
        src_stalks = stalks[:, self.src_idx, :]  # (batch, 2, stalk_dim)
        dst_stalks = stalks[:, self.dst_idx, :]  # (batch, 2, stalk_dim)
        
        src_probs = probs[:, self.src_idx, :]
        dst_probs = probs[:, self.dst_idx, :]
        
        # Apply restriction (learned function)
        restricted_src = self.restriction(src_stalks)
        
        g = self.get_mixture_weight()
        
        # Attractive flow: push z towards function of inputs
        attr_flow = restricted_src - dst_stalks
        
        # Repulsive flow: push z away from inputs
        overlap = (src_probs * dst_probs).sum(dim=-1, keepdim=True)
        repl_flow = -overlap * (restricted_src - dst_stalks)
        
        # Mix
        flow = g * attr_flow + (1 - g) * repl_flow
        
        # Aggregate flow to dst (z)
        drift = torch.zeros_like(stalks)
        drift[:, 2, :] = dt * flow.sum(dim=1)  # Sum contributions from x and y
        
        # Thermal noise
        temp = temperature.view(-1, 1, 1)
        noise_std = self.noise_scale * torch.sqrt(2 * temp * dt + 1e-8)
        thermal_noise = noise_std * torch.randn_like(stalks)
        
        new_stalks = stalks + drift + thermal_noise
        
        # Clamp clues (x, y are given)
        clue_mask_expanded = clue_mask.unsqueeze(-1)
        new_stalks = torch.where(clue_mask_expanded, stalks, new_stalks)
        
        return new_stalks


class ArithmeticAgent(nn.Module):
    """Agent for modular arithmetic with adaptive polarity."""
    
    def __init__(self, config: ArithmeticConfig):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(11, config.stalk_dim)  # 0-9 + unknown
        
        edges, _ = build_arithmetic_graph()
        self.diffusion = ArithmeticDiffusion(
            stalk_dim=config.stalk_dim,
            num_digits=config.num_digits,
            edges=edges,
            polarity_init=config.polarity_init,
            noise_scale=config.noise_scale,
        )
        
        self.output_head = nn.Linear(config.stalk_dim, config.num_digits)
        
        # Simple arousal based on pain EMA
        self.register_buffer('pain_ema', torch.tensor(1.0))
        self.tau = config.tau
        self.min_temp = config.min_temp
    
    def update_pain(self, pain: torch.Tensor):
        with torch.no_grad():
            self.pain_ema = 0.95 * self.pain_ema + 0.05 * pain
    
    def get_temperature(self) -> torch.Tensor:
        arousal = torch.sigmoid((self.pain_ema - self.tau) / max(self.tau, 0.1))
        return torch.clamp(arousal, min=self.min_temp)
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None):
        batch_size = puzzles.shape[0]
        device = puzzles.device
        
        # Clue mask: x and y are given (positions 0, 1)
        clue_mask = torch.zeros(batch_size, 3, dtype=torch.bool, device=device)
        clue_mask[:, 0] = True  # x is given
        clue_mask[:, 1] = True  # y is given
        
        stalks = self.embed(puzzles)
        temperature = self.get_temperature()
        
        for _ in range(self.config.diffusion_steps):
            logits = self.output_head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, 
                                            self.config.diffusion_dt, clue_mask, temperature)
        
        logits = self.output_head(stalks)
        
        energy, g = self.diffusion.compute_energies(logits)
        
        # Task pain (only for z, position 2)
        task_pain = torch.tensor(0.0, device=device)
        if solutions is not None:
            z_logits = logits[:, 2, :]  # (batch, 10)
            task_pain = F.cross_entropy(z_logits, solutions)
            self.update_pain(task_pain.detach())
        
        return logits, energy, g, temperature


def run_test():
    """Run the arithmetic validation test."""
    device = "cuda" if torch.cuda.is_available() else "cpu"
    config = ArithmeticConfig()
    
    model = ArithmeticAgent(config).to(device)
    
    # Generate data
    train_puzzles, train_solutions = generate_arithmetic_data(5000, seed=42)
    test_puzzles, test_solutions = generate_arithmetic_data(1000, seed=1042)
    
    train_dataset = TensorDataset(
        torch.tensor(train_puzzles, dtype=torch.long),
        torch.tensor(train_solutions, dtype=torch.long),
    )
    test_dataset = TensorDataset(
        torch.tensor(test_puzzles, dtype=torch.long),
        torch.tensor(test_solutions, dtype=torch.long),
    )
    
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    # Optimizer
    polarity_params = [model.diffusion.polarity_logit]
    other_params = [p for p in model.parameters() if id(p) != id(model.diffusion.polarity_logit)]
    
    optimizer = torch.optim.AdamW([
        {'params': other_params, 'lr': config.lr, 'weight_decay': 0.01},
        {'params': polarity_params, 'lr': config.polarity_lr, 'weight_decay': 0.0},
    ])
    
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=config.epochs)
    
    # Logging
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/run_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 100)
    print("VALIDATION TEST: Modular Arithmetic (x + y = z mod 10)")
    print("=" * 100)
    print(f"Device: {device}")
    print(f"Initial Mixture Weight (g): {model.diffusion.get_mixture_weight().item():.3f}")
    print(f"TensorBoard: {log_path}")
    print("=" * 100)
    print()
    print("CRITICAL TEST: Should learn g -> 1.0 (ATTRACTION)")
    print("  If g -> 0 (Repulsion), our theory is WRONG!")
    print()
    
    print("-" * 80)
    print(f" {'Epoch':>5} | {'Train Acc':>9} | {'Test Acc':>8} | {'g (polarity)':>12} | {'Temp':>6} | Status")
    print("-" * 80)
    
    best_acc = 0.0
    
    for epoch in range(config.epochs):
        model.train()
        
        for batch in train_loader:
            puzzles, solutions = [x.to(device) for x in batch]
            
            optimizer.zero_grad()
            
            logits, energy, g, temp = model(puzzles, solutions)
            
            z_logits = logits[:, 2, :]
            loss = F.cross_entropy(z_logits, solutions) + 0.1 * energy
            
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
        
        scheduler.step()
        
        # Evaluate
        if epoch % config.log_interval == 0:
            model.eval()
            correct = 0
            total = 0
            with torch.no_grad():
                for batch in test_loader:
                    puzzles, solutions = [x.to(device) for x in batch]
                    logits, *_ = model(puzzles)
                    z_preds = logits[:, 2, :].argmax(dim=-1)
                    correct += (z_preds == solutions).sum().item()
                    total += solutions.shape[0]
            
            test_acc = correct / total
            g_val = model.diffusion.get_mixture_weight().item()
            temp_val = model.get_temperature().item()
            
            status = ""
            if test_acc > best_acc:
                best_acc = test_acc
                status = "BEST"
            if g_val > 0.7:
                status += " ATTRACTION!"
            elif g_val < 0.3:
                status += " REPULSION (BAD!)"
            
            print(f" {epoch:>5} | {0:>8.1f}% | {test_acc*100:>7.1f}% | {g_val:>12.3f} | {temp_val:>6.3f} | {status}")
            
            writer.add_scalar("test/acc", test_acc, epoch)
            writer.add_scalar("polarity/g", g_val, epoch)
            writer.add_scalar("thermo/temp", temp_val, epoch)
    
    # Final verdict
    final_g = model.diffusion.get_mixture_weight().item()
    print("=" * 100)
    print(f"FINAL RESULTS: Best Acc={best_acc*100:.1f}%, g={final_g:.3f}")
    print()
    if final_g > 0.7 and best_acc > 0.9:
        print("THEORY VALIDATED: Agent learned ATTRACTION for arithmetic!")
        print("   Combined with Sudoku results (g->0), we have proven:")
        print("   - Repulsive constraints (x != y) -> g -> 0")
        print("   - Attractive constraints (f(x,y) = z) -> g -> 1")
    elif final_g > 0.5:
        print("PARTIAL: Agent trending towards attraction, may need more training.")
    else:
        print("THEORY FALSIFIED: Agent learned repulsion for arithmetic!")
        print("   This contradicts our hypothesis. Need to investigate.")
    print("=" * 100)
    
    writer.close()
    return model


if __name__ == "__main__":
    model = run_test()
