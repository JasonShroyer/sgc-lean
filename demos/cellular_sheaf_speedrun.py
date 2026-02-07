"""
Cellular Sheaf Network: Speed Run Experiment
=============================================

Hypothesis: Grokking epoch drops from ~975 to <300 via:
1. Stalk Noise: Inject noise during diffusion for robustness
2. Curriculum Learning: Train addition first, then unlock multiplication

Based on Perplexity synthesis (Feb 7, 2026):
- Noise "vibrates the stalks" → widens funnel to global section
- Curriculum mimics biological learning (kids learn + before *)

Date: 2026-02-07
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
import numpy as np
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional
from datetime import datetime
import os


@dataclass
class SpeedRunConfig:
    """Configuration for Speed Run experiment."""
    p: int = 23                    # Modulus (small for speed)
    stalk_dim: int = 64            # Dimension of each stalk
    embed_dim: int = 32            # Input embedding dimension
    diffusion_steps: int = 20      # Steps of Sheaf diffusion
    diffusion_dt: float = 0.1      # Time step for diffusion
    epochs: int = 1000
    lr: float = 1e-3
    weight_decay: float = 0.1
    batch_size: int = 512
    seed: int = 42
    
    # Speed Run additions
    stalk_noise: float = 0.1       # Noise injected during diffusion
    noise_decay: float = 0.995     # Noise decay per epoch
    curriculum_epochs: int = 200   # Epochs to train addition only
    curriculum_enabled: bool = True


class SheafCell(nn.Module):
    """A single cell (node) in the cellular sheaf."""
    
    def __init__(self, stalk_dim: int, is_input: bool = False, is_output: bool = False,
                 input_dim: int = None, output_dim: int = None):
        super().__init__()
        self.stalk_dim = stalk_dim
        self.is_input = is_input
        self.is_output = is_output
        
        if is_input and input_dim is not None:
            self.input_proj = nn.Linear(input_dim, stalk_dim)
        
        if is_output and output_dim is not None:
            self.output_proj = nn.Linear(stalk_dim, output_dim)
    
    def set_from_input(self, x: torch.Tensor) -> torch.Tensor:
        assert self.is_input, "Cell is not an input cell"
        return self.input_proj(x)
    
    def get_output(self, stalk_value: torch.Tensor) -> torch.Tensor:
        assert self.is_output, "Cell is not an output cell"
        return self.output_proj(stalk_value)


class RestrictionMap(nn.Module):
    """Non-linear restriction map between two stalks."""
    
    def __init__(self, source_dim: int, target_dim: int, hidden_dim: int = None):
        super().__init__()
        hidden_dim = hidden_dim or max(source_dim, target_dim) * 2
        
        self.net = nn.Sequential(
            nn.Linear(source_dim, hidden_dim),
            nn.GELU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.GELU(),
            nn.Linear(hidden_dim, target_dim),
        )
        
        # Standard initialization
        for layer in self.net:
            if isinstance(layer, nn.Linear):
                nn.init.xavier_uniform_(layer.weight)
                nn.init.zeros_(layer.bias)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class SpeedRunSheafNetwork(nn.Module):
    """
    Cellular Sheaf Network with Speed Run enhancements.
    
    Enhancements:
    1. Stalk noise during diffusion
    2. Curriculum learning support (freeze multiplication path)
    """
    
    def __init__(self, config: SpeedRunConfig):
        super().__init__()
        self.config = config
        
        # Embedding for inputs
        self.embed = nn.Embedding(config.p, config.embed_dim)
        
        # Cells (stalks)
        self.cell_x = SheafCell(config.stalk_dim, is_input=True, input_dim=config.embed_dim)
        self.cell_y = SheafCell(config.stalk_dim, is_input=True, input_dim=config.embed_dim)
        self.cell_z = SheafCell(config.stalk_dim, is_input=True, input_dim=config.embed_dim)
        self.cell_sum = SheafCell(config.stalk_dim)
        self.cell_result = SheafCell(config.stalk_dim, is_output=True, output_dim=config.p)
        
        # Restriction maps (edges)
        self.rho_x_sum = RestrictionMap(config.stalk_dim, config.stalk_dim)
        self.rho_y_sum = RestrictionMap(config.stalk_dim, config.stalk_dim)
        self.rho_sum_result = RestrictionMap(config.stalk_dim, config.stalk_dim)
        self.rho_z_result = RestrictionMap(config.stalk_dim, config.stalk_dim)
        
        # Learnable diffusion gate
        self.diffusion_gate = nn.Parameter(torch.tensor(0.0))
        
        # Current noise level (decays during training)
        self.current_noise = config.stalk_noise
        
        # Curriculum phase
        self.curriculum_phase = "addition"  # "addition" or "full"
    
    def set_curriculum_phase(self, phase: str):
        """Set curriculum phase: 'addition' or 'full'."""
        self.curriculum_phase = phase
        if phase == "addition":
            # Freeze multiplication path
            for param in self.rho_z_result.parameters():
                param.requires_grad = False
            for param in self.rho_sum_result.parameters():
                param.requires_grad = False
        else:
            # Unfreeze all
            for param in self.rho_z_result.parameters():
                param.requires_grad = True
            for param in self.rho_sum_result.parameters():
                param.requires_grad = True
    
    def decay_noise(self):
        """Decay noise level."""
        self.current_noise *= self.config.noise_decay
    
    def diffusion_step(
        self,
        v_x: torch.Tensor, v_y: torch.Tensor, v_z: torch.Tensor,
        v_sum: torch.Tensor, v_result: torch.Tensor,
        dt: float, training: bool = True
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        One step of Sheaf diffusion with stalk noise.
        """
        gate = torch.sigmoid(self.diffusion_gate)
        
        # Message passing to SUM node
        msg_x = self.rho_x_sum(v_x)
        msg_y = self.rho_y_sum(v_y)
        v_sum_target = msg_x + msg_y
        
        # Inject stalk noise (only during training)
        if training and self.current_noise > 0:
            noise = torch.randn_like(v_sum) * self.current_noise
            v_sum_target = v_sum_target + noise
        
        v_sum_new = (1 - dt * gate) * v_sum + dt * gate * v_sum_target
        
        # Message passing to RESULT node
        msg_sum = self.rho_sum_result(v_sum_new)
        msg_z = self.rho_z_result(v_z)
        v_result_target = msg_sum * msg_z  # Multiplicative aggregation
        
        # Inject stalk noise
        if training and self.current_noise > 0:
            noise = torch.randn_like(v_result) * self.current_noise
            v_result_target = v_result_target + noise
        
        v_result_new = (1 - dt * gate) * v_result + dt * gate * v_result_target
        
        return v_sum_new, v_result_new
    
    def forward(self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor]:
        """Forward pass via Sheaf Diffusion with noise."""
        batch_size = x.shape[0]
        device = x.device
        training = self.training
        
        # Set boundary conditions
        e_x = self.embed(x)
        e_y = self.embed(y)
        e_z = self.embed(z)
        
        v_x = self.cell_x.set_from_input(e_x)
        v_y = self.cell_y.set_from_input(e_y)
        v_z = self.cell_z.set_from_input(e_z)
        
        # Initialize intermediate nodes
        v_sum = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        v_result = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        
        # Run Sheaf diffusion
        for _ in range(self.config.diffusion_steps):
            v_sum, v_result = self.diffusion_step(
                v_x, v_y, v_z, v_sum, v_result,
                dt=self.config.diffusion_dt,
                training=training
            )
        
        # Compute final energy (without noise for clean measurement)
        energy = self.compute_energy(v_x, v_y, v_z, v_sum, v_result)
        
        # Output projection
        logits = self.cell_result.get_output(v_result)
        
        return logits, energy.mean()
    
    def compute_energy(self, v_x, v_y, v_z, v_sum, v_result) -> torch.Tensor:
        """Compute Sheaf Laplacian energy."""
        e_x_sum = (self.rho_x_sum(v_x) - v_sum).pow(2).sum(dim=-1)
        e_y_sum = (self.rho_y_sum(v_y) - v_sum).pow(2).sum(dim=-1)
        e_sum_result = (self.rho_sum_result(v_sum) - v_result).pow(2).sum(dim=-1)
        e_z_result = (self.rho_z_result(v_z) - v_result).pow(2).sum(dim=-1)
        return e_x_sum + e_y_sum + e_sum_result + e_z_result


def create_composition_dataset(p: int, train_frac: float = 0.3):
    """Create dataset for (x + y) * z mod p."""
    all_data = []
    for x in range(p):
        for y in range(p):
            for z in range(p):
                target = ((x + y) * z) % p
                all_data.append((x, y, z, target))
    
    all_data = np.array(all_data)
    np.random.shuffle(all_data)
    
    n_train = int(len(all_data) * train_frac)
    train_data = all_data[:n_train]
    test_data = all_data[n_train:]
    
    train_dataset = TensorDataset(
        torch.tensor(train_data[:, 0], dtype=torch.long),
        torch.tensor(train_data[:, 1], dtype=torch.long),
        torch.tensor(train_data[:, 2], dtype=torch.long),
        torch.tensor(train_data[:, 3], dtype=torch.long)
    )
    test_dataset = TensorDataset(
        torch.tensor(test_data[:, 0], dtype=torch.long),
        torch.tensor(test_data[:, 1], dtype=torch.long),
        torch.tensor(test_data[:, 2], dtype=torch.long),
        torch.tensor(test_data[:, 3], dtype=torch.long)
    )
    
    return train_dataset, test_dataset


def create_addition_dataset(p: int, train_frac: float = 0.3):
    """Create dataset for (x + y) mod p (curriculum phase 1)."""
    all_data = []
    for x in range(p):
        for y in range(p):
            target = (x + y) % p
            all_data.append((x, y, target))
    
    all_data = np.array(all_data)
    np.random.shuffle(all_data)
    
    n_train = int(len(all_data) * train_frac)
    train_data = all_data[:n_train]
    test_data = all_data[n_train:]
    
    train_dataset = TensorDataset(
        torch.tensor(train_data[:, 0], dtype=torch.long),
        torch.tensor(train_data[:, 1], dtype=torch.long),
        torch.tensor(train_data[:, 2], dtype=torch.long)
    )
    test_dataset = TensorDataset(
        torch.tensor(test_data[:, 0], dtype=torch.long),
        torch.tensor(test_data[:, 1], dtype=torch.long),
        torch.tensor(test_data[:, 2], dtype=torch.long)
    )
    
    return train_dataset, test_dataset


def evaluate(model: SpeedRunSheafNetwork, dataloader: DataLoader, device: str) -> Tuple[float, float]:
    """Evaluate accuracy and mean energy."""
    model.eval()
    correct = 0
    total = 0
    total_energy = 0.0
    
    with torch.no_grad():
        for batch in dataloader:
            x, y, z, target = [b.to(device) for b in batch]
            logits, energy = model(x, y, z)
            pred = logits.argmax(dim=-1)
            correct += (pred == target).sum().item()
            total += target.shape[0]
            total_energy += energy.item() * target.shape[0]
    
    return correct / total, total_energy / total


def run_speedrun_experiment(config: SpeedRunConfig):
    """
    Run the Speed Run experiment.
    
    Phase 1: Train addition only (curriculum)
    Phase 2: Unlock multiplication
    """
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    print("=" * 80)
    print("CELLULAR SHEAF NETWORK: SPEED RUN")
    print("=" * 80)
    print(f"Device: {device}")
    print(f"Config: p={config.p}, stalk_noise={config.stalk_noise}, curriculum_epochs={config.curriculum_epochs}")
    print(f"Hypothesis: Grokking in <300 epochs (baseline ~975)")
    print("=" * 80)
    
    # Create datasets
    train_dataset, test_dataset = create_composition_dataset(config.p, train_frac=0.3)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = SpeedRunSheafNetwork(config).to(device)
    
    total_params = sum(p.numel() for p in model.parameters())
    trainable_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    print(f"Parameters: {trainable_params:,} trainable / {total_params:,} total")
    
    # Optimizer
    optimizer = torch.optim.AdamW(
        model.parameters(),
        lr=config.lr,
        weight_decay=config.weight_decay
    )
    
    # TensorBoard
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"logs/speedrun/run_{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"TensorBoard: {log_dir}")
    
    # Training loop
    print("\n" + "-" * 80)
    print(" Epoch |   Train |    Test |   Noise |   Energy | Phase")
    print("-" * 80)
    
    best_test_acc = 0.0
    grokked = False
    grok_epoch = None
    
    # Phase tracking
    if config.curriculum_enabled:
        model.set_curriculum_phase("addition")
        current_phase = "addition"
    else:
        model.set_curriculum_phase("full")
        current_phase = "full"
    
    for epoch in range(config.epochs):
        # Curriculum transition
        if config.curriculum_enabled and epoch == config.curriculum_epochs:
            print(f"\n>>> CURRICULUM TRANSITION: Unlocking multiplication path <<<\n")
            model.set_curriculum_phase("full")
            current_phase = "full"
            # Re-create optimizer to include unfrozen params
            optimizer = torch.optim.AdamW(
                filter(lambda p: p.requires_grad, model.parameters()),
                lr=config.lr,
                weight_decay=config.weight_decay
            )
        
        model.train()
        epoch_loss = 0.0
        epoch_energy = 0.0
        
        for batch in train_loader:
            x, y, z, target = [b.to(device) for b in batch]
            
            optimizer.zero_grad()
            logits, energy = model(x, y, z)
            
            ce_loss = F.cross_entropy(logits, target)
            loss = ce_loss + 0.01 * energy
            
            loss.backward()
            optimizer.step()
            
            epoch_loss += loss.item()
            epoch_energy += energy.item()
        
        # Decay noise
        model.decay_noise()
        
        # Evaluate every 25 epochs
        if epoch % 25 == 0 or epoch == config.epochs - 1:
            train_acc, train_energy = evaluate(model, train_loader, device)
            test_acc, test_energy = evaluate(model, test_loader, device)
            
            # Log to TensorBoard
            writer.add_scalar('Accuracy/Train', train_acc, epoch)
            writer.add_scalar('Accuracy/Test', test_acc, epoch)
            writer.add_scalar('Energy/Train', train_energy, epoch)
            writer.add_scalar('Noise/Current', model.current_noise, epoch)
            
            # Status
            status = current_phase.upper()
            if test_acc > 0.99 and not grokked:
                grokked = True
                grok_epoch = epoch
                status = "*** GROKKED ***"
            elif test_acc > best_test_acc:
                best_test_acc = test_acc
                status = f"{current_phase} (best)"
            
            print(f" {epoch:5d} | {train_acc:7.1%} | {test_acc:7.1%} | {model.current_noise:7.4f} | {train_energy:8.2f} | {status}")
        
        # Early stopping on grokking
        if grokked and epoch > grok_epoch + 50:
            print(f"\n>>> Early stopping: Grokked at epoch {grok_epoch} <<<")
            break
    
    writer.close()
    
    # Final report
    print("\n" + "=" * 80)
    print("SPEED RUN RESULTS")
    print("=" * 80)
    if grokked:
        print(f"  GROKKED at epoch {grok_epoch}")
        speedup = 975 / grok_epoch if grok_epoch > 0 else float('inf')
        print(f"  Speedup: {speedup:.1f}x vs baseline (~975 epochs)")
    else:
        print(f"  Did NOT grok within {config.epochs} epochs")
        print(f"  Best test accuracy: {best_test_acc:.1%}")
    print(f"  Final noise level: {model.current_noise:.6f}")
    print("=" * 80)
    
    return model, grok_epoch


if __name__ == "__main__":
    config = SpeedRunConfig(
        p=23,
        epochs=1000,
        stalk_noise=0.1,
        noise_decay=0.995,
        curriculum_epochs=200,
        curriculum_enabled=True,
        seed=42
    )
    
    model, grok_epoch = run_speedrun_experiment(config)
