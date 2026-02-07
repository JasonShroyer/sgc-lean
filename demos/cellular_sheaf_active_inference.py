"""
Cellular Sheaf Network: Active Inference Edition
=================================================

Implements Perplexity's suggestions (Feb 7, 2026):
1. Precision-Weighted Sheaf: Learnable γ per edge (not scalar noise)
2. Scaffolded Training: Teacher forcing on v_sum (topologically valid curriculum)
3. Active Inference terminology: Diffusion → Perceptual Inference

Key insight: The 98.5% plateau was a request for PRECISION, not just noise decay.

Free Energy Objective:
    F = Σ γ_e ||ρ(u) - v||² + λ Σ log(γ_e)
      = Accuracy (precision-weighted) - Complexity (precision penalty)

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
class ActiveInferenceConfig:
    """Configuration for Active Inference Sheaf Network."""
    p: int = 23                    # Modulus
    stalk_dim: int = 64            # Dimension of each stalk
    embed_dim: int = 32            # Input embedding dimension
    diffusion_steps: int = 20      # Steps of perceptual inference
    diffusion_dt: float = 0.1      # Time step
    epochs: int = 1500
    lr: float = 1e-3
    weight_decay: float = 0.1
    batch_size: int = 512
    seed: int = 42
    
    # Active Inference parameters
    precision_lr: float = 0.01     # Learning rate for precision params
    precision_penalty: float = 0.01  # Complexity penalty on log-precision
    
    # Scaffolding parameters
    scaffold_epochs: int = 300     # Epochs of teacher forcing on v_sum
    scaffold_blend: float = 0.5    # Blend factor (1.0 = full forcing, 0.0 = free)


class SheafCell(nn.Module):
    """A single cell (stalk) in the cellular sheaf."""
    
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
        return self.input_proj(x)
    
    def get_output(self, stalk_value: torch.Tensor) -> torch.Tensor:
        return self.output_proj(stalk_value)


class RestrictionMap(nn.Module):
    """Non-linear restriction map (edge morphism) between stalks."""
    
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
        
        for layer in self.net:
            if isinstance(layer, nn.Linear):
                nn.init.xavier_uniform_(layer.weight)
                nn.init.zeros_(layer.bias)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class ActiveInferenceSheafNetwork(nn.Module):
    """
    Cellular Sheaf Network with Active Inference dynamics.
    
    Key innovations:
    1. Learnable precision (γ) per edge - attention mechanism
    2. Free Energy objective: Accuracy - Complexity
    3. Scaffolded training support for teacher forcing
    
    Terminology mapping:
    - Diffusion step → Perceptual Inference (state estimation)
    - Restriction map update → Learning (parameter estimation)
    - Precision update → Attention (precision estimation)
    """
    
    def __init__(self, config: ActiveInferenceConfig):
        super().__init__()
        self.config = config
        
        # Embedding
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
        
        # ACTIVE INFERENCE: Learnable precision per edge (log-space for stability)
        # γ = exp(log_precision) ensures positivity
        self.log_precision = nn.Parameter(torch.zeros(4))  # [x→sum, y→sum, sum→result, z→result]
        
        # Learnable diffusion gate
        self.diffusion_gate = nn.Parameter(torch.tensor(0.0))
        
        # For scaffolding: projection to create "teacher" v_sum from true (x+y)
        self.sum_teacher_proj = nn.Linear(config.embed_dim, config.stalk_dim)
    
    def get_precisions(self) -> torch.Tensor:
        """Get precision values (positive)."""
        return torch.exp(self.log_precision)
    
    def compute_edge_energies(self, v_x, v_y, v_z, v_sum, v_result) -> Dict[str, torch.Tensor]:
        """Compute prediction error for each edge."""
        return {
            'x_sum': (self.rho_x_sum(v_x) - v_sum).pow(2).sum(dim=-1),
            'y_sum': (self.rho_y_sum(v_y) - v_sum).pow(2).sum(dim=-1),
            'sum_result': (self.rho_sum_result(v_sum) - v_result).pow(2).sum(dim=-1),
            'z_result': (self.rho_z_result(v_z) - v_result).pow(2).sum(dim=-1),
        }
    
    def compute_free_energy(self, edge_energies: Dict[str, torch.Tensor]) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        Compute variational Free Energy.
        
        F = Accuracy + Complexity
          = Σ γ_e * E_e + λ * Σ (log(γ_e))²
        
        The complexity term penalizes deviation from γ=1 (log(γ)=0).
        This prevents both precision collapse (γ→0) and explosion (γ→∞).
        """
        precisions = self.get_precisions()
        
        # Precision-weighted accuracy (prediction errors)
        accuracy = (
            precisions[0] * edge_energies['x_sum'] +
            precisions[1] * edge_energies['y_sum'] +
            precisions[2] * edge_energies['sum_result'] +
            precisions[3] * edge_energies['z_result']
        )
        
        # Complexity: penalize deviation from γ=1 (quadratic in log-space)
        # This keeps precision near 1 unless there's strong evidence to change it
        complexity = self.config.precision_penalty * (self.log_precision ** 2).sum()
        
        return accuracy.mean(), complexity
    
    def perceptual_inference_step(
        self,
        v_x: torch.Tensor, v_y: torch.Tensor, v_z: torch.Tensor,
        v_sum: torch.Tensor, v_result: torch.Tensor,
        dt: float,
        teacher_sum: Optional[torch.Tensor] = None,
        scaffold_weight: float = 0.0
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        One step of Perceptual Inference (state estimation).
        
        This is the "E-step" of Active Inference: update beliefs about hidden states
        given the current generative model (restriction maps).
        """
        gate = torch.sigmoid(self.diffusion_gate)
        
        # Message passing to SUM node (additive aggregation)
        msg_x = self.rho_x_sum(v_x)
        msg_y = self.rho_y_sum(v_y)
        v_sum_inferred = msg_x + msg_y
        
        # SCAFFOLDING: Blend with teacher signal if provided
        if teacher_sum is not None and scaffold_weight > 0:
            v_sum_target = (1 - scaffold_weight) * v_sum_inferred + scaffold_weight * teacher_sum
        else:
            v_sum_target = v_sum_inferred
        
        v_sum_new = (1 - dt * gate) * v_sum + dt * gate * v_sum_target
        
        # Message passing to RESULT node (multiplicative aggregation)
        msg_sum = self.rho_sum_result(v_sum_new)
        msg_z = self.rho_z_result(v_z)
        v_result_target = msg_sum * msg_z
        
        v_result_new = (1 - dt * gate) * v_result + dt * gate * v_result_target
        
        return v_sum_new, v_result_new
    
    def forward(
        self, 
        x: torch.Tensor, y: torch.Tensor, z: torch.Tensor,
        sum_labels: Optional[torch.Tensor] = None,
        scaffold_weight: float = 0.0
    ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Forward pass via Perceptual Inference.
        
        Args:
            x, y, z: Input tensors
            sum_labels: Optional (x+y) mod p labels for scaffolding
            scaffold_weight: How much to blend teacher signal (0=free, 1=forced)
        
        Returns:
            logits: Output predictions
            free_energy: Variational free energy
            complexity: Precision complexity term
        """
        batch_size = x.shape[0]
        device = x.device
        
        # Set boundary conditions (sensory observations)
        e_x = self.embed(x)
        e_y = self.embed(y)
        e_z = self.embed(z)
        
        v_x = self.cell_x.set_from_input(e_x)
        v_y = self.cell_y.set_from_input(e_y)
        v_z = self.cell_z.set_from_input(e_z)
        
        # Compute teacher signal for scaffolding
        teacher_sum = None
        if sum_labels is not None and scaffold_weight > 0:
            e_sum = self.embed(sum_labels)
            teacher_sum = self.sum_teacher_proj(e_sum)
        
        # Initialize hidden states (prior beliefs)
        v_sum = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        v_result = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        
        # Run Perceptual Inference (iterative belief updating)
        for _ in range(self.config.diffusion_steps):
            v_sum, v_result = self.perceptual_inference_step(
                v_x, v_y, v_z, v_sum, v_result,
                dt=self.config.diffusion_dt,
                teacher_sum=teacher_sum,
                scaffold_weight=scaffold_weight
            )
        
        # Compute Free Energy
        edge_energies = self.compute_edge_energies(v_x, v_y, v_z, v_sum, v_result)
        free_energy, complexity = self.compute_free_energy(edge_energies)
        
        # Output projection
        logits = self.cell_result.get_output(v_result)
        
        return logits, free_energy, complexity


def create_composition_dataset(p: int, train_frac: float = 0.3):
    """Create dataset for (x + y) * z mod p with intermediate labels."""
    all_data = []
    for x in range(p):
        for y in range(p):
            for z in range(p):
                target = ((x + y) * z) % p
                sum_xy = (x + y) % p  # Intermediate label for scaffolding
                all_data.append((x, y, z, target, sum_xy))
    
    all_data = np.array(all_data)
    np.random.shuffle(all_data)
    
    n_train = int(len(all_data) * train_frac)
    train_data = all_data[:n_train]
    test_data = all_data[n_train:]
    
    def make_dataset(data):
        return TensorDataset(
            torch.tensor(data[:, 0], dtype=torch.long),
            torch.tensor(data[:, 1], dtype=torch.long),
            torch.tensor(data[:, 2], dtype=torch.long),
            torch.tensor(data[:, 3], dtype=torch.long),
            torch.tensor(data[:, 4], dtype=torch.long),  # sum labels
        )
    
    return make_dataset(train_data), make_dataset(test_data)


def evaluate(model: ActiveInferenceSheafNetwork, dataloader: DataLoader, device: str) -> Tuple[float, float]:
    """Evaluate accuracy and mean free energy."""
    model.eval()
    correct = 0
    total = 0
    total_fe = 0.0
    
    with torch.no_grad():
        for batch in dataloader:
            x, y, z, target, _ = [b.to(device) for b in batch]
            logits, fe, _ = model(x, y, z)  # No scaffolding during eval
            pred = logits.argmax(dim=-1)
            correct += (pred == target).sum().item()
            total += target.shape[0]
            total_fe += fe.item() * target.shape[0]
    
    return correct / total, total_fe / total


def run_active_inference_experiment(config: ActiveInferenceConfig):
    """
    Run the Active Inference Sheaf experiment.
    
    Phase 1 (Scaffolded): Teacher forcing on v_sum
    Phase 2 (Free): Pure perceptual inference
    """
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    print("=" * 80)
    print("ACTIVE INFERENCE SHEAF NETWORK")
    print("=" * 80)
    print(f"Device: {device}")
    print(f"Config: p={config.p}, scaffold_epochs={config.scaffold_epochs}")
    print(f"Precision penalty: {config.precision_penalty}")
    print("=" * 80)
    
    # Create datasets
    train_dataset, test_dataset = create_composition_dataset(config.p, train_frac=0.3)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = ActiveInferenceSheafNetwork(config).to(device)
    
    total_params = sum(p.numel() for p in model.parameters())
    print(f"Parameters: {total_params:,}")
    
    # Separate optimizer for precision parameters
    main_params = [p for n, p in model.named_parameters() if 'log_precision' not in n]
    precision_params = [model.log_precision]
    
    optimizer = torch.optim.AdamW([
        {'params': main_params, 'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': precision_params, 'lr': config.precision_lr, 'weight_decay': 0.0},
    ])
    
    # TensorBoard
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"logs/active_inference/run_{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"TensorBoard: {log_dir}")
    
    # Training loop
    print("\n" + "-" * 90)
    print(" Epoch |   Train |    Test |      FE |  g_x>s |  g_y>s | g_s>r |  g_z>r | Phase")
    print("-" * 90)
    
    best_test_acc = 0.0
    grokked = False
    grok_epoch = None
    
    for epoch in range(config.epochs):
        # Compute scaffold weight (linear decay)
        if epoch < config.scaffold_epochs:
            scaffold_weight = config.scaffold_blend * (1 - epoch / config.scaffold_epochs)
            phase = f"scaffold({scaffold_weight:.2f})"
        else:
            scaffold_weight = 0.0
            phase = "free"
        
        model.train()
        epoch_loss = 0.0
        
        for batch in train_loader:
            x, y, z, target, sum_labels = [b.to(device) for b in batch]
            
            optimizer.zero_grad()
            logits, free_energy, complexity = model(
                x, y, z, 
                sum_labels=sum_labels,
                scaffold_weight=scaffold_weight
            )
            
            # Total loss: classification + free energy
            ce_loss = F.cross_entropy(logits, target)
            loss = ce_loss + 0.01 * free_energy + complexity
            
            loss.backward()
            optimizer.step()
            
            epoch_loss += loss.item()
        
        # Evaluate every 25 epochs
        if epoch % 25 == 0 or epoch == config.epochs - 1:
            train_acc, train_fe = evaluate(model, train_loader, device)
            test_acc, test_fe = evaluate(model, test_loader, device)
            
            # Get precision values
            prec = model.get_precisions().detach().cpu().numpy()
            
            # Log to TensorBoard
            writer.add_scalar('Accuracy/Train', train_acc, epoch)
            writer.add_scalar('Accuracy/Test', test_acc, epoch)
            writer.add_scalar('FreeEnergy/Train', train_fe, epoch)
            writer.add_scalar('Precision/x_sum', prec[0], epoch)
            writer.add_scalar('Precision/y_sum', prec[1], epoch)
            writer.add_scalar('Precision/sum_result', prec[2], epoch)
            writer.add_scalar('Precision/z_result', prec[3], epoch)
            writer.add_scalar('Scaffold/Weight', scaffold_weight, epoch)
            
            # Status
            status = phase
            if test_acc > 0.99 and not grokked:
                grokked = True
                grok_epoch = epoch
                status = "*** GROKKED ***"
            elif test_acc > best_test_acc:
                best_test_acc = test_acc
                status = f"{phase} (best)"
            
            print(f" {epoch:5d} | {train_acc:7.1%} | {test_acc:7.1%} | {train_fe:7.2f} | "
                  f"{prec[0]:6.2f} | {prec[1]:6.2f} | {prec[2]:5.2f} | {prec[3]:6.2f} | {status}")
        
        # Early stopping
        if grokked and epoch > grok_epoch + 50:
            print(f"\n>>> Early stopping: Grokked at epoch {grok_epoch} <<<")
            break
    
    writer.close()
    
    # Final report
    print("\n" + "=" * 80)
    print("ACTIVE INFERENCE RESULTS")
    print("=" * 80)
    if grokked:
        print(f"  ✓ GROKKED at epoch {grok_epoch}")
        baseline = 975
        speedup = baseline / grok_epoch if grok_epoch > 0 else float('inf')
        print(f"  Speedup: {speedup:.1f}x vs baseline (~{baseline} epochs)")
    else:
        print(f"  Did NOT grok within {config.epochs} epochs")
        print(f"  Best test accuracy: {best_test_acc:.1%}")
    
    prec = model.get_precisions().detach().cpu().numpy()
    print(f"\n  Final Precisions:")
    print(f"    γ(x→sum):    {prec[0]:.4f}")
    print(f"    γ(y→sum):    {prec[1]:.4f}")
    print(f"    γ(sum→res):  {prec[2]:.4f}")
    print(f"    γ(z→res):    {prec[3]:.4f}")
    print("=" * 80)
    
    return model, grok_epoch


if __name__ == "__main__":
    config = ActiveInferenceConfig(
        p=23,
        epochs=1500,
        scaffold_epochs=300,
        scaffold_blend=0.5,
        precision_penalty=0.01,
        seed=42
    )
    
    model, grok_epoch = run_active_inference_experiment(config)
