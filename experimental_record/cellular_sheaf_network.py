"""
Cellular Sheaf Network: Native Geometric Computation

This implements Option C from the Phase 2 analysis - a network where the
sheaf structure IS the computation, not an analysis tool applied post-hoc.

Architecture:
- Base Space: Cellular complex (graph) of concept nodes
- Stalks: Learnable vector spaces at each node
- Restriction Maps: Trainable matrices on edges
- Learning: Dissipative (minimize Sheaf Laplacian energy for correct outputs)

Task: Compositional modular arithmetic (x + y) * z mod p

The key insight: Instead of retrofitting sheaf logic onto neural networks,
we BUILD the network as a sheaf. The geometry is native.
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
class CellularConfig:
    """Configuration for Cellular Sheaf Network."""
    p: int = 97                    # Modulus
    stalk_dim: int = 64            # Dimension of each stalk
    embed_dim: int = 32            # Input embedding dimension
    diffusion_steps: int = 20      # Steps of Sheaf diffusion
    diffusion_dt: float = 0.1      # Time step for diffusion
    epochs: int = 2000
    lr: float = 1e-3
    weight_decay: float = 0.1
    batch_size: int = 512
    seed: int = 42


class SheafCell(nn.Module):
    """
    A single cell (node) in the cellular sheaf.
    
    Each cell has:
    - A stalk (vector space)
    - Input projection (for input nodes)
    - Output projection (for output nodes)
    """
    
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
        """Project input into stalk space."""
        assert self.is_input, "Cell is not an input cell"
        return self.input_proj(x)
    
    def get_output(self, stalk_value: torch.Tensor) -> torch.Tensor:
        """Project stalk value to output space."""
        assert self.is_output, "Cell is not an output cell"
        return self.output_proj(stalk_value)


class RestrictionMap(nn.Module):
    """
    Non-linear restriction map between two stalks.
    
    Implements rho_{e}: F(head(e)) -> F(tail(e))
    Uses an MLP for expressivity - can learn non-linear transformations.
    """
    
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
        
        # Initialize with reasonable scale (not too small for multiplicative)
        for layer in self.net:
            if isinstance(layer, nn.Linear):
                nn.init.xavier_uniform_(layer.weight, gain=1.0)
                nn.init.zeros_(layer.bias)
    
    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x)


class CellularSheafNetwork(nn.Module):
    """
    Cellular Sheaf Network for Compositional Modular Arithmetic.
    
    Graph Structure (for (x + y) * z):
    
        [X] ----rho_x----> [SUM] ----rho_sum----> [RESULT]
             \            /                      /
              \          /                      /
        [Y] --rho_y---->/                      /
                                              /
        [Z] -----------rho_z---------------->/
    
    The sheaf structure:
    - Nodes: X, Y, Z (inputs), SUM (intermediate), RESULT (output)
    - Stalks: Vector spaces at each node
    - Edges: Connections with learnable restriction maps
    
    Computation via Sheaf Diffusion:
    1. Fix input node values from embeddings
    2. Initialize other nodes to zero
    3. Run diffusion to minimize Laplacian energy
    4. Read output from RESULT node
    """
    
    def __init__(self, config: CellularConfig):
        super().__init__()
        self.config = config
        p = config.p
        stalk_dim = config.stalk_dim
        embed_dim = config.embed_dim
        
        # Input embeddings (shared across all input types)
        self.embed = nn.Embedding(p, embed_dim)
        
        # Cells (nodes in the sheaf)
        self.cell_x = SheafCell(stalk_dim, is_input=True, input_dim=embed_dim)
        self.cell_y = SheafCell(stalk_dim, is_input=True, input_dim=embed_dim)
        self.cell_z = SheafCell(stalk_dim, is_input=True, input_dim=embed_dim)
        self.cell_sum = SheafCell(stalk_dim)  # Intermediate node for x+y
        self.cell_result = SheafCell(stalk_dim, is_output=True, output_dim=p)
        
        # Restriction maps (edges)
        # Edge: X -> SUM
        self.rho_x_sum = RestrictionMap(stalk_dim, stalk_dim)
        # Edge: Y -> SUM
        self.rho_y_sum = RestrictionMap(stalk_dim, stalk_dim)
        # Edge: SUM -> RESULT
        self.rho_sum_result = RestrictionMap(stalk_dim, stalk_dim)
        # Edge: Z -> RESULT
        self.rho_z_result = RestrictionMap(stalk_dim, stalk_dim)
        
        # Learnable diffusion parameters
        self.diffusion_gate = nn.Parameter(torch.tensor(0.5))
        
    def compute_laplacian_energy(
        self,
        v_x: torch.Tensor, v_y: torch.Tensor, v_z: torch.Tensor,
        v_sum: torch.Tensor, v_result: torch.Tensor
    ) -> torch.Tensor:
        """
        Compute the Sheaf Laplacian energy.
        
        E = sum over edges of ||rho(head) - tail||^2
        
        Lower energy = more consistent section (stalks agree under restriction)
        """
        # Edge X -> SUM: disagreement
        e_x_sum = (self.rho_x_sum(v_x) - v_sum).pow(2).sum(dim=-1)
        
        # Edge Y -> SUM: disagreement
        e_y_sum = (self.rho_y_sum(v_y) - v_sum).pow(2).sum(dim=-1)
        
        # Edge SUM -> RESULT: disagreement
        e_sum_result = (self.rho_sum_result(v_sum) - v_result).pow(2).sum(dim=-1)
        
        # Edge Z -> RESULT: disagreement
        e_z_result = (self.rho_z_result(v_z) - v_result).pow(2).sum(dim=-1)
        
        # Total energy
        energy = e_x_sum + e_y_sum + e_sum_result + e_z_result
        return energy
    
    def diffusion_step(
        self,
        v_x: torch.Tensor, v_y: torch.Tensor, v_z: torch.Tensor,
        v_sum: torch.Tensor, v_result: torch.Tensor,
        dt: float
    ) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        One step of non-linear Sheaf diffusion.
        
        Instead of linear gradient flow, we use message passing:
        v_i = aggregate(transform(neighbors))
        
        Input nodes (x, y, z) are FIXED - they are boundary conditions.
        Only intermediate nodes (sum, result) evolve.
        """
        gate = torch.sigmoid(self.diffusion_gate)
        
        # Message passing to SUM node: aggregate transformed X and Y
        msg_x = self.rho_x_sum(v_x)
        msg_y = self.rho_y_sum(v_y)
        # Aggregate: sum of incoming messages (captures addition structure)
        v_sum_target = msg_x + msg_y
        # Interpolate toward target
        v_sum_new = (1 - dt * gate) * v_sum + dt * gate * v_sum_target
        
        # Message passing to RESULT node: aggregate transformed SUM and Z
        msg_sum = self.rho_sum_result(v_sum_new)
        msg_z = self.rho_z_result(v_z)
        # Aggregate: element-wise product (captures multiplication structure!)
        v_result_target = msg_sum * msg_z
        # Interpolate toward target
        v_result_new = (1 - dt * gate) * v_result + dt * gate * v_result_target
        
        return v_sum_new, v_result_new
    
    def forward(self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor]:
        """
        Forward pass via Sheaf Diffusion.
        
        1. Embed inputs and project to stalks (boundary conditions)
        2. Initialize intermediate nodes
        3. Run diffusion to find harmonic section
        4. Read output from result node
        
        Returns: (logits, final_energy)
        """
        batch_size = x.shape[0]
        device = x.device
        
        # 1. Set boundary conditions (input nodes)
        e_x = self.embed(x)
        e_y = self.embed(y)
        e_z = self.embed(z)
        
        v_x = self.cell_x.set_from_input(e_x)
        v_y = self.cell_y.set_from_input(e_y)
        v_z = self.cell_z.set_from_input(e_z)
        
        # 2. Initialize intermediate nodes (start at zero or learned prior)
        v_sum = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        v_result = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        
        # 3. Run Sheaf diffusion
        for _ in range(self.config.diffusion_steps):
            v_sum, v_result = self.diffusion_step(
                v_x, v_y, v_z, v_sum, v_result,
                dt=self.config.diffusion_dt
            )
        
        # 4. Compute final energy (for monitoring)
        energy = self.compute_laplacian_energy(v_x, v_y, v_z, v_sum, v_result)
        
        # 5. Read output
        logits = self.cell_result.get_output(v_result)
        
        return logits, energy.mean()
    
    def get_stalk_representations(
        self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor
    ) -> Dict[str, torch.Tensor]:
        """Get all stalk values after diffusion (for analysis)."""
        batch_size = x.shape[0]
        device = x.device
        
        e_x = self.embed(x)
        e_y = self.embed(y)
        e_z = self.embed(z)
        
        v_x = self.cell_x.set_from_input(e_x)
        v_y = self.cell_y.set_from_input(e_y)
        v_z = self.cell_z.set_from_input(e_z)
        
        v_sum = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        v_result = torch.zeros(batch_size, self.config.stalk_dim, device=device)
        
        for _ in range(self.config.diffusion_steps):
            v_sum, v_result = self.diffusion_step(
                v_x, v_y, v_z, v_sum, v_result,
                dt=self.config.diffusion_dt
            )
        
        return {
            'x': v_x, 'y': v_y, 'z': v_z,
            'sum': v_sum, 'result': v_result
        }


def create_composition_dataset(p: int, train_frac: float = 0.3):
    """
    Create dataset for (x + y) * z mod p.
    
    We use a smaller train fraction to test compositional generalization.
    """
    all_triples = [(x, y, z) for x in range(p) for y in range(p) for z in range(p)]
    np.random.shuffle(all_triples)
    
    n_train = int(len(all_triples) * train_frac)
    train_triples = all_triples[:n_train]
    test_triples = all_triples[n_train:]
    
    def to_tensors(triples):
        x = torch.tensor([t[0] for t in triples], dtype=torch.long)
        y = torch.tensor([t[1] for t in triples], dtype=torch.long)
        z = torch.tensor([t[2] for t in triples], dtype=torch.long)
        target = torch.tensor([((t[0] + t[1]) * t[2]) % p for t in triples], dtype=torch.long)
        return x, y, z, target
    
    train_x, train_y, train_z, train_t = to_tensors(train_triples)
    test_x, test_y, test_z, test_t = to_tensors(test_triples)
    
    train_dataset = TensorDataset(train_x, train_y, train_z, train_t)
    test_dataset = TensorDataset(test_x, test_y, test_z, test_t)
    
    return train_dataset, test_dataset


def compute_functional_defect(
    model: CellularSheafNetwork,
    dataloader: DataLoader,
    num_classes: int,
    device: str,
    node: str = 'result'
) -> float:
    """
    Compute functional defect (eps) for a specific stalk.
    
    eps = within_class_variance / total_variance
    Low eps = good class separation = grokked representation
    """
    model.eval()
    all_hidden = []
    all_labels = []
    
    with torch.no_grad():
        for batch in dataloader:
            x, y, z, target = [b.to(device) for b in batch]
            stalks = model.get_stalk_representations(x, y, z)
            hidden = stalks[node]
            all_hidden.append(hidden)
            all_labels.append(target)
    
    hidden = torch.cat(all_hidden, dim=0).float()
    labels = torch.cat(all_labels, dim=0)
    
    total_var = hidden.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 1.0
    
    within_var = 0.0
    total_count = 0
    
    for c in range(num_classes):
        mask = (labels == c)
        count = mask.sum().item()
        if count > 1:
            class_h = hidden[mask]
            class_var = class_h.var(dim=0).mean().item()
            within_var += class_var * count
            total_count += count
    
    if total_count > 0:
        within_var /= total_count
    
    eps = within_var / (total_var + 1e-10)
    return eps


def evaluate(model: CellularSheafNetwork, dataloader: DataLoader, device: str) -> Tuple[float, float]:
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


def run_cellular_sheaf_experiment(config: CellularConfig):
    """
    Run the Cellular Sheaf Network experiment.
    
    This is the "Native Geometry" approach - the network IS a sheaf.
    """
    # Setup
    torch.manual_seed(config.seed)
    np.random.seed(config.seed)
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    
    print("=" * 80)
    print("CELLULAR SHEAF NETWORK: Native Geometric Computation")
    print("=" * 80)
    print(f"Device: {device}")
    print(f"Config: p={config.p}, stalk_dim={config.stalk_dim}, diffusion_steps={config.diffusion_steps}")
    print(f"Task: (x + y) * z mod {config.p}")
    print("=" * 80)
    
    # Create datasets
    train_dataset, test_dataset = create_composition_dataset(config.p, train_frac=0.3)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)
    test_loader = DataLoader(test_dataset, batch_size=config.batch_size)
    
    print(f"\nDataset: {len(train_dataset)} train, {len(test_dataset)} test")
    
    # Create model
    model = CellularSheafNetwork(config).to(device)
    
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
    log_dir = f"logs/cellular_sheaf/run_{timestamp}"
    writer = SummaryWriter(log_dir)
    print(f"TensorBoard: {log_dir}")
    
    # Training loop
    print("\n" + "-" * 80)
    print(" Epoch |   Train |    Test |     eps |   Energy | Status")
    print("-" * 80)
    
    best_test_acc = 0.0
    grokked = False
    grok_epoch = None
    
    for epoch in range(config.epochs):
        model.train()
        epoch_loss = 0.0
        epoch_energy = 0.0
        
        for batch in train_loader:
            x, y, z, target = [b.to(device) for b in batch]
            
            optimizer.zero_grad()
            logits, energy = model(x, y, z)
            
            # Classification loss + energy regularization
            ce_loss = F.cross_entropy(logits, target)
            loss = ce_loss + 0.01 * energy  # Small energy penalty
            
            loss.backward()
            optimizer.step()
            
            epoch_loss += loss.item()
            epoch_energy += energy.item()
        
        # Evaluate every 25 epochs
        if epoch % 25 == 0 or epoch == config.epochs - 1:
            train_acc, train_energy = evaluate(model, train_loader, device)
            test_acc, test_energy = evaluate(model, test_loader, device)
            eps = compute_functional_defect(model, train_loader, config.p, device, 'result')
            
            # Check for grokking
            status = ""
            if test_acc > best_test_acc:
                best_test_acc = test_acc
            
            if not grokked and test_acc > 0.99 and eps < 0.15:
                grokked = True
                grok_epoch = epoch
                status = "<-- GROKKED!"
            elif test_acc > 0.90:
                status = "<-- Learning!"
            
            print(f"{epoch:6d} | {train_acc:6.1%} | {test_acc:6.1%} | {eps:7.4f} | {test_energy:8.2f} | {status}")
            
            # TensorBoard
            writer.add_scalar('Accuracy/train', train_acc, epoch)
            writer.add_scalar('Accuracy/test', test_acc, epoch)
            writer.add_scalar('Metrics/eps', eps, epoch)
            writer.add_scalar('Metrics/energy', test_energy, epoch)
            
            # Early stopping on grokking
            if grokked and epoch > grok_epoch + 100:
                print("\n[Early Stop] Grokked and stable")
                break
    
    writer.close()
    
    # Final summary
    print("\n" + "=" * 80)
    print("EXPERIMENT SUMMARY")
    print("=" * 80)
    
    final_train_acc, _ = evaluate(model, train_loader, device)
    final_test_acc, final_energy = evaluate(model, test_loader, device)
    final_eps = compute_functional_defect(model, train_loader, config.p, device, 'result')
    
    print(f"\nFinal Results:")
    print(f"  Train Accuracy: {final_train_acc:.1%}")
    print(f"  Test Accuracy:  {final_test_acc:.1%}")
    print(f"  Functional Defect (eps): {final_eps:.4f}")
    print(f"  Sheaf Energy: {final_energy:.2f}")
    
    if grokked:
        print(f"\n  GROKKED at epoch {grok_epoch}!")
        print("  The Cellular Sheaf Network achieved compositional generalization!")
    else:
        print(f"\n  Best test accuracy: {best_test_acc:.1%}")
        print("  Did not fully grok, but may still be learning.")
    
    print("-" * 80)
    
    # Analyze restriction maps
    print("\n[Restriction Map Analysis]")
    with torch.no_grad():
        for name, rho in [
            ('rho_x_sum', model.rho_x_sum),
            ('rho_y_sum', model.rho_y_sum),
            ('rho_sum_result', model.rho_sum_result),
            ('rho_z_result', model.rho_z_result),
        ]:
            W = rho.linear.weight
            identity = torch.eye(W.shape[0], device=W.device)
            deviation = (W - identity).norm().item()
            print(f"  {name}: deviation from identity = {deviation:.4f}")
    
    return model, {'train_acc': final_train_acc, 'test_acc': final_test_acc, 
                   'eps': final_eps, 'energy': final_energy, 'grokked': grokked}


if __name__ == "__main__":
    config = CellularConfig(
        p=23,              # Smaller prime for faster iteration (23^3 = 12K vs 97^3 = 912K)
        stalk_dim=64,
        embed_dim=32,
        diffusion_steps=20,
        diffusion_dt=0.1,
        epochs=3000,
        lr=1e-3,
        weight_decay=0.1,
        seed=42,
    )
    
    model, results = run_cellular_sheaf_experiment(config)
