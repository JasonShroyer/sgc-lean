"""
Cellular Sheaf Network: Homeostatic Precision Controller
=========================================================

Implements the "Cybernetic Geometry" architecture (Feb 7, 2026):
- Slow (Structure): Learned precision prior (the Metric / Laplacian)
- Fast (Control): Homeostatic arousal (the Envelope / Temperature)

Key insight: Precision is both GEOMETRY (what to trust) and CONTROL (when to explore).

Theoretical mapping:
| Component          | SGC                  | Active Inference      | Biology            |
|--------------------|----------------------|-----------------------|--------------------|
| Learned Prior      | Laplacian L          | Policy Precision      | Synaptic Weight    |
| Fast Modulation    | Envelope B(t)        | Expected Precision    | Neuromodulation    |

The Homeostatic Controller:
    gamma_eff = gamma_prior * (1 - sigmoid((E_ema - tau) / tau))
    
    - Error > Target: High arousal -> Low precision -> Explore/Melt
    - Error < Target: Low arousal -> High precision -> Exploit/Freeze

Date: 2026-02-07
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
import numpy as np
from dataclasses import dataclass
from typing import Dict, Tuple, Optional
from datetime import datetime


@dataclass
class HomeostaticConfig:
    """Configuration for Homeostatic Sheaf Network."""
    p: int = 23
    stalk_dim: int = 64
    embed_dim: int = 32
    diffusion_steps: int = 20
    diffusion_dt: float = 0.1
    epochs: int = 1500
    lr: float = 1e-3
    weight_decay: float = 0.1
    batch_size: int = 512
    seed: int = 42
    
    # Homeostatic parameters
    precision_lr: float = 0.01
    precision_penalty: float = 0.01
    tau: float = 5.0          # Homeostatic target (set-point) - tuned to typical energy scale
    ema_alpha: float = 0.95   # Smoothing factor for energy EMA
    min_precision: float = 0.1  # Floor on effective precision (prevents collapse)
    
    # Scaffolding
    scaffold_epochs: int = 300
    scaffold_blend: float = 0.5


class HomeostaticPrecision(nn.Module):
    """
    Homeostatic Precision Controller.
    
    Combines:
    - Slow: Learned precision prior (the Geometry)
    - Fast: Arousal-based modulation (the Control)
    
    The effective precision adapts to current error:
    - High error -> High arousal -> Low precision -> Explore
    - Low error -> Low arousal -> High precision -> Exploit
    """
    
    def __init__(self, num_edges: int, tau: float = 0.1, alpha: float = 0.9):
        super().__init__()
        self.num_edges = num_edges
        self.tau = tau
        self.alpha = alpha
        
        # Slow: Learned geometry (the Laplacian structure)
        self.log_precision_prior = nn.Parameter(torch.zeros(num_edges))
        
        # Fast: Running state (not learned, just tracked)
        self.register_buffer('energy_ema', torch.ones(num_edges) * tau)
    
    def forward(self, current_energies: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Compute effective precision given current edge energies.
        
        Args:
            current_energies: Per-edge energies [num_edges]
        
        Returns:
            effective_precision: Modulated precision [num_edges]
            arousal: Current arousal level [num_edges]
            prior_precision: The learned prior [num_edges]
        """
        # 1. Update fast state (no gradients through EMA history)
        with torch.no_grad():
            self.energy_ema.mul_(self.alpha).add_(current_energies.detach(), alpha=1-self.alpha)
        
        # 2. Compute Arousal (Control Signal)
        # Deviation from homeostatic target
        deviation = (self.energy_ema - self.tau) / (self.tau + 1e-8)
        arousal = torch.sigmoid(deviation)
        
        # 3. Combine: Effective Precision = Geometry * (1 - 0.9*Arousal)
        # The 0.9 factor ensures precision never fully collapses
        prior_precision = torch.exp(self.log_precision_prior)
        effective_precision = prior_precision * (1.0 - 0.9 * arousal)
        
        return effective_precision, arousal, prior_precision
    
    def complexity_loss(self) -> torch.Tensor:
        """Quadratic prior penalty on log-precision (keeps gamma near 1)."""
        return (self.log_precision_prior ** 2).sum()


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
    """Non-linear restriction map between stalks."""
    
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


class HomeostaticSheafNetwork(nn.Module):
    """
    Cellular Sheaf Network with Homeostatic Precision Controller.
    
    Architecture:
    - Stalks: x, y, z (inputs), sum (intermediate), result (output)
    - Edges: x->sum, y->sum (addition), sum->result, z->result (multiplication)
    - Precision: Homeostatic controller (slow geometry + fast arousal)
    """
    
    def __init__(self, config: HomeostaticConfig):
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
        # Edge indices: 0=x->sum, 1=y->sum, 2=sum->result, 3=z->result
        self.rho_x_sum = RestrictionMap(config.stalk_dim, config.stalk_dim)      # Edge 0
        self.rho_y_sum = RestrictionMap(config.stalk_dim, config.stalk_dim)      # Edge 1
        self.rho_sum_result = RestrictionMap(config.stalk_dim, config.stalk_dim) # Edge 2
        self.rho_z_result = RestrictionMap(config.stalk_dim, config.stalk_dim)   # Edge 3
        
        # Homeostatic Precision Controller
        self.precision_controller = HomeostaticPrecision(
            num_edges=4,
            tau=config.tau,
            alpha=config.ema_alpha
        )
        
        # Diffusion gate
        self.diffusion_gate = nn.Parameter(torch.tensor(0.0))
        
        # Teacher projection for scaffolding
        self.sum_teacher_proj = nn.Linear(config.embed_dim, config.stalk_dim)
    
    def compute_edge_energies(self, v_x, v_y, v_z, v_sum, v_result) -> torch.Tensor:
        """Compute per-edge prediction errors. Returns [4] tensor."""
        e0 = (self.rho_x_sum(v_x) - v_sum).pow(2).sum(dim=-1).mean()      # x->sum
        e1 = (self.rho_y_sum(v_y) - v_sum).pow(2).sum(dim=-1).mean()      # y->sum
        e2 = (self.rho_sum_result(v_sum) - v_result).pow(2).sum(dim=-1).mean()  # sum->result
        e3 = (self.rho_z_result(v_z) - v_result).pow(2).sum(dim=-1).mean()      # z->result
        return torch.stack([e0, e1, e2, e3])
    
    def compute_free_energy(self, edge_energies: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Compute Free Energy with homeostatic precision.
        
        Returns:
            free_energy: Total free energy
            complexity: Prior penalty
            arousal: Current arousal levels [4]
            effective_precision: Current effective precision [4]
        """
        effective_precision, arousal, prior_precision = self.precision_controller(edge_energies)
        
        # Precision-weighted accuracy
        accuracy = (effective_precision * edge_energies).sum()
        
        # Complexity (quadratic prior on log-precision)
        complexity = self.config.precision_penalty * self.precision_controller.complexity_loss()
        
        free_energy = accuracy + complexity
        
        return free_energy, complexity, arousal, effective_precision
    
    def perceptual_inference_step(
        self,
        v_x: torch.Tensor, v_y: torch.Tensor, v_z: torch.Tensor,
        v_sum: torch.Tensor, v_result: torch.Tensor,
        dt: float,
        teacher_sum: Optional[torch.Tensor] = None,
        scaffold_weight: float = 0.0
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """One step of perceptual inference (belief updating)."""
        gate = torch.sigmoid(self.diffusion_gate)
        
        # Message passing to SUM node
        msg_x = self.rho_x_sum(v_x)
        msg_y = self.rho_y_sum(v_y)
        v_sum_inferred = msg_x + msg_y
        
        # Scaffolding blend
        if teacher_sum is not None and scaffold_weight > 0:
            v_sum_target = (1 - scaffold_weight) * v_sum_inferred + scaffold_weight * teacher_sum
        else:
            v_sum_target = v_sum_inferred
        
        v_sum_new = (1 - dt * gate) * v_sum + dt * gate * v_sum_target
        
        # Message passing to RESULT node
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
    ) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Forward pass with homeostatic precision.
        
        Returns:
            logits, free_energy, complexity, arousal, effective_precision
        """
        batch_size = x.shape[0]
        device = x.device
        
        # Embed inputs
        e_x = self.embed(x)
        e_y = self.embed(y)
        e_z = self.embed(z)
        
        v_x = self.cell_x.set_from_input(e_x)
        v_y = self.cell_y.set_from_input(e_y)
        v_z = self.cell_z.set_from_input(e_z)
        
        # Teacher signal
        teacher_sum = None
        if sum_labels is not None and scaffold_weight > 0:
            e_sum = self.embed(sum_labels)
            teacher_sum = self.sum_teacher_proj(e_sum)
        
        # Initialize hidden states
        v_sum = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        v_result = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        
        # Perceptual inference loop
        for _ in range(self.config.diffusion_steps):
            v_sum, v_result = self.perceptual_inference_step(
                v_x, v_y, v_z, v_sum, v_result,
                dt=self.config.diffusion_dt,
                teacher_sum=teacher_sum,
                scaffold_weight=scaffold_weight
            )
        
        # Compute energies and free energy
        edge_energies = self.compute_edge_energies(v_x, v_y, v_z, v_sum, v_result)
        free_energy, complexity, arousal, effective_precision = self.compute_free_energy(edge_energies)
        
        # Output
        logits = self.cell_result.get_output(v_result)
        
        return logits, free_energy, complexity, arousal, effective_precision


def create_composition_dataset(p: int, train_frac: float = 0.3):
    """Create dataset for (x + y) * z mod p with intermediate labels."""
    all_data = []
    for x in range(p):
        for y in range(p):
            for z in range(p):
                target = ((x + y) * z) % p
                sum_xy = (x + y) % p
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
            torch.tensor(data[:, 4], dtype=torch.long),
        )
    
    return make_dataset(train_data), make_dataset(test_data)


def evaluate(model: HomeostaticSheafNetwork, dataloader: DataLoader, device: str) -> Tuple[float, float]:
    """Evaluate accuracy and mean free energy."""
    model.eval()
    correct = 0
    total = 0
    total_fe = 0.0
    
    with torch.no_grad():
        for batch in dataloader:
            x, y, z, target, _ = [b.to(device) for b in batch]
            logits, fe, _, _, _ = model(x, y, z)
            pred = logits.argmax(dim=-1)
            correct += (pred == target).sum().item()
            total += target.shape[0]
            total_fe += fe.item() * target.shape[0]
    
    return correct / total, total_fe / total


def run_homeostatic_experiment(config: HomeostaticConfig):
    """Run the Homeostatic Sheaf experiment."""
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    print("=" * 90)
    print("HOMEOSTATIC SHEAF NETWORK (Cybernetic Geometry)")
    print("=" * 90)
    print(f"Device: {device}")
    print(f"Config: p={config.p}, tau={config.tau}, ema_alpha={config.ema_alpha}")
    print("=" * 90)
    
    # Create datasets
    train_dataset, test_dataset = create_composition_dataset(config.p, train_frac=0.3)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = HomeostaticSheafNetwork(config).to(device)
    
    total_params = sum(p.numel() for p in model.parameters())
    print(f"Parameters: {total_params:,}")
    
    # Optimizer with separate LR for precision
    main_params = [p for n, p in model.named_parameters() if 'log_precision' not in n]
    precision_params = [model.precision_controller.log_precision_prior]
    
    optimizer = torch.optim.AdamW([
        {'params': main_params, 'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': precision_params, 'lr': config.precision_lr, 'weight_decay': 0.0},
    ])
    
    # TensorBoard
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = f"logs/homeostatic/run_{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"TensorBoard: {log_dir}")
    
    # Training loop
    print("\n" + "-" * 110)
    print(" Epoch |  Train |   Test |    FE | g_x>s | g_y>s | g_s>r | g_z>r | a_x>s | a_y>s | a_s>r | a_z>r | Phase")
    print("-" * 110)
    
    best_test_acc = 0.0
    grokked = False
    grok_epoch = None
    
    for epoch in range(config.epochs):
        # Scaffold weight
        if epoch < config.scaffold_epochs:
            scaffold_weight = config.scaffold_blend * (1 - epoch / config.scaffold_epochs)
            phase = f"scaffold({scaffold_weight:.2f})"
        else:
            scaffold_weight = 0.0
            phase = "free"
        
        model.train()
        
        for batch in train_loader:
            x, y, z, target, sum_labels = [b.to(device) for b in batch]
            
            optimizer.zero_grad()
            logits, free_energy, complexity, arousal, eff_prec = model(
                x, y, z,
                sum_labels=sum_labels,
                scaffold_weight=scaffold_weight
            )
            
            ce_loss = F.cross_entropy(logits, target)
            loss = ce_loss + 0.01 * free_energy + complexity
            
            loss.backward()
            optimizer.step()
        
        # Evaluate every 25 epochs
        if epoch % 25 == 0 or epoch == config.epochs - 1:
            train_acc, train_fe = evaluate(model, train_loader, device)
            test_acc, test_fe = evaluate(model, test_loader, device)
            
            # Get current precision and arousal
            with torch.no_grad():
                # Run one forward to get current state
                x_sample = torch.zeros(1, dtype=torch.long, device=device)
                _, _, _, arousal, eff_prec = model(x_sample, x_sample, x_sample)
                arousal = arousal.cpu().numpy()
                eff_prec = eff_prec.cpu().numpy()
                prior_prec = torch.exp(model.precision_controller.log_precision_prior).cpu().numpy()
            
            # TensorBoard logging
            writer.add_scalar('Accuracy/Train', train_acc, epoch)
            writer.add_scalar('Accuracy/Test', test_acc, epoch)
            writer.add_scalar('FreeEnergy/Train', train_fe, epoch)
            for i, name in enumerate(['x_sum', 'y_sum', 'sum_result', 'z_result']):
                writer.add_scalar(f'Precision_Prior/{name}', prior_prec[i], epoch)
                writer.add_scalar(f'Precision_Effective/{name}', eff_prec[i], epoch)
                writer.add_scalar(f'Arousal/{name}', arousal[i], epoch)
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
            
            print(f" {epoch:5d} | {train_acc:6.1%} | {test_acc:6.1%} | {train_fe:5.2f} | "
                  f"{eff_prec[0]:5.2f} | {eff_prec[1]:5.2f} | {eff_prec[2]:5.2f} | {eff_prec[3]:5.2f} | "
                  f"{arousal[0]:5.2f} | {arousal[1]:5.2f} | {arousal[2]:5.2f} | {arousal[3]:5.2f} | {status}")
        
        # Early stopping
        if grokked and epoch > grok_epoch + 50:
            print(f"\n>>> Early stopping: Grokked at epoch {grok_epoch} <<<")
            break
    
    writer.close()
    
    # Final report
    print("\n" + "=" * 90)
    print("HOMEOSTATIC RESULTS")
    print("=" * 90)
    if grokked:
        print(f"  GROKKED at epoch {grok_epoch}")
        baseline = 975
        speedup = baseline / grok_epoch if grok_epoch > 0 else float('inf')
        print(f"  Speedup: {speedup:.2f}x vs baseline (~{baseline} epochs)")
    else:
        print(f"  Did NOT grok within {config.epochs} epochs")
        print(f"  Best test accuracy: {best_test_acc:.1%}")
    
    print(f"\n  Final State:")
    print(f"    Prior Precision:     [{prior_prec[0]:.3f}, {prior_prec[1]:.3f}, {prior_prec[2]:.3f}, {prior_prec[3]:.3f}]")
    print(f"    Effective Precision: [{eff_prec[0]:.3f}, {eff_prec[1]:.3f}, {eff_prec[2]:.3f}, {eff_prec[3]:.3f}]")
    print(f"    Arousal:             [{arousal[0]:.3f}, {arousal[1]:.3f}, {arousal[2]:.3f}, {arousal[3]:.3f}]")
    print("=" * 90)
    
    return model, grok_epoch


if __name__ == "__main__":
    config = HomeostaticConfig(
        p=23,
        epochs=1500,
        scaffold_epochs=300,
        scaffold_blend=0.5,
        precision_penalty=0.01,
        tau=5.0,       # Tuned to typical energy scale (~10-20)
        ema_alpha=0.95,
        seed=42
    )
    
    model, grok_epoch = run_homeostatic_experiment(config)
