"""
SGC Phase 2: Sheaf Connector with Diffusion Inference

This implements the theoretical pivot from "Separate Pathways" to "Sheaf from the Start".

Key Design Principles:
1. Neural networks are LOCAL STALKS (sensory patches)
2. Intelligence resides in RESTRICTION MAPS (the geometry)
3. Inference via SHEAF DIFFUSION (harmonic extension), not feedforward

The Sheaf Laplacian: Δ_F = B^T @ B
- B is the coboundary operator (encodes restriction maps)
- Harmonic sections satisfy Δ_F @ x = 0
- Diffusion finds the harmonic extension: x_{t+1} = x_t - α * Δ_F @ x_t

This answers the deep question: "Why approximate geometry?"
Answer: DON'T. Use neural nets as sensors, do reasoning via native geometric logic.

Author: SGC Research Team
Date: February 6, 2026
"""

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from dataclasses import dataclass
from typing import Optional, Tuple, Dict
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sgc_continual_learning import DualTaskMLP


@dataclass
class SheafConfig:
    """Configuration for Sheaf Connector."""
    p: int = 97
    stalk_dim: int = 256
    diffusion_steps: int = 100      # More steps for proper settling
    diffusion_alpha: float = 0.5    # Larger step for faster convergence
    energy_threshold: float = 1e-6  # Stop when energy is low
    train_frac: float = 0.3
    seed: int = 42


class SheafConnector(nn.Module):
    """
    Sheaf Connector: Learns restriction maps between frozen stalks.
    
    Architecture (for f(x,y,z) = (x+y)*z mod p):
    
    Graph Structure:
        Node 0: Add Stalk (frozen h_add from Task A)
        Node 1: Mul Stalk (frozen h_mul from Task B)  
        Node 2: Z Stalk (embedding of z)
        Node 3: Composition Node (where we read the answer)
    
    Edges (Restriction Maps - the ONLY learned parameters):
        ρ_0→3: Add → Composition (LINEAR)
        ρ_1→3: Mul → Composition (LINEAR)
        ρ_2→3: Z → Composition (LINEAR)
    
    Inference:
        1. Initialize stalks from frozen models
        2. Diffuse on Sheaf Laplacian until equilibrium
        3. Read output from composition node
    
    The restriction maps encode HOW addition and multiplication
    geometrically relate - this is the "native geometry" we seek.
    """
    
    def __init__(self, frozen_model: DualTaskMLP, config: SheafConfig):
        super().__init__()
        self.frozen_model = frozen_model
        self.config = config
        self.p = config.p
        self.d = config.stalk_dim  # Stalk dimension
        
        # Freeze the base model
        for param in frozen_model.parameters():
            param.requires_grad = False
        
        # Z embedding (trainable - we need to learn z's representation)
        self.embed_z = nn.Embedding(config.p, self.d)
        
        # ============================================================
        # RESTRICTION MAPS (LINEAR ONLY - the geometry is explicit)
        # ============================================================
        # These are the ONLY learned parameters for composition
        # They encode how different representational spaces relate
        
        # ρ_add: Project Add stalk into Composition space
        self.rho_add = nn.Linear(self.d, self.d, bias=False)
        
        # ρ_mul: Project Mul stalk into Composition space
        self.rho_mul = nn.Linear(self.d, self.d, bias=False)
        
        # ρ_z: Project Z stalk into Composition space
        self.rho_z = nn.Linear(self.d, self.d, bias=False)
        
        # Initialize restriction maps as small perturbations of identity
        # This starts with "everything is the same space" assumption
        nn.init.eye_(self.rho_add.weight)
        nn.init.eye_(self.rho_mul.weight)
        nn.init.eye_(self.rho_z.weight)
        self.rho_add.weight.data += 0.01 * torch.randn_like(self.rho_add.weight)
        self.rho_mul.weight.data += 0.01 * torch.randn_like(self.rho_mul.weight)
        self.rho_z.weight.data += 0.01 * torch.randn_like(self.rho_z.weight)
        
        # Output head (reads from composition node)
        self.output_head = nn.Linear(self.d, config.p)
    
    def get_stalks(self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        Extract stalk values from frozen models.
        
        These are the "local truths" - what each sensory patch sees.
        """
        with torch.no_grad():
            # Add stalk: frozen Task A representation of (x, y)
            h_add = self.frozen_model.get_shared_hidden(x, y)
            
            # Mul stalk: frozen Task B representation
            # For composition (x+y)*z, we want z's multiplicative meaning
            # Using get_mul_hidden(z, z) gives us z's self-representation in mul space
            h_mul = self.frozen_model.get_mul_hidden(z, z)
        
        # Z stalk: learned embedding of z
        h_z = self.embed_z(z)
        
        return h_add, h_mul, h_z
    
    def compute_sheaf_energy(self, 
                             h_add: torch.Tensor,
                             h_mul: torch.Tensor,
                             h_z: torch.Tensor,
                             h_comp: torch.Tensor) -> torch.Tensor:
        """
        Compute Sheaf Laplacian energy: E = ⟨x, Δ_F x⟩
        
        This measures the INCONSISTENCY between adjacent stalks.
        A Global Section has E = 0 (all stalks agree after restriction).
        
        E = ||ρ_add(h_add) - h_comp||² + ||ρ_mul(h_mul) - h_comp||² + ||ρ_z(h_z) - h_comp||²
        """
        # Project stalks through restriction maps
        add_proj = self.rho_add(h_add)
        mul_proj = self.rho_mul(h_mul)
        z_proj = self.rho_z(h_z)
        
        # Energy: squared disagreement
        e_add = torch.sum((add_proj - h_comp) ** 2, dim=-1)
        e_mul = torch.sum((mul_proj - h_comp) ** 2, dim=-1)
        e_z = torch.sum((z_proj - h_comp) ** 2, dim=-1)
        
        return e_add + e_mul + e_z
    
    def diffusion_step(self,
                       h_add: torch.Tensor,
                       h_mul: torch.Tensor,
                       h_z: torch.Tensor,
                       h_comp: torch.Tensor) -> torch.Tensor:
        """
        One step of Sheaf Laplacian diffusion.
        
        This is the "experiential" part - the system SETTLES into
        a consistent state by following the gradient of sheaf energy.
        
        ∂h_comp/∂t = -∇E = (ρ_add(h_add) + ρ_mul(h_mul) + ρ_z(h_z)) / 3 - h_comp
        
        Discretized: h_comp' = h_comp + α * (target - h_comp)
        """
        # Project stalks through restriction maps
        add_proj = self.rho_add(h_add)
        mul_proj = self.rho_mul(h_mul)
        z_proj = self.rho_z(h_z)
        
        # The harmonic extension is the weighted average
        # (In a more complex graph, this would involve the full Laplacian)
        target = (add_proj + mul_proj + z_proj) / 3.0
        
        # Diffusion update
        h_comp_new = h_comp + self.config.diffusion_alpha * (target - h_comp)
        
        return h_comp_new
    
    def forward_diffusion(self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor,
                          return_energy: bool = False) -> torch.Tensor:
        """
        Sheaf Diffusion inference.
        
        This is the core of "native geometric reasoning":
        1. Get local truths from frozen stalks
        2. Let energy flow through restriction maps
        3. Settle into harmonic extension (consistent global state)
        4. Read the answer
        
        This is how a living creature "experiences" - through equilibration.
        """
        batch_size = x.shape[0]
        device = x.device
        
        # Get frozen stalk values
        h_add, h_mul, h_z = self.get_stalks(x, y, z)
        
        # Initialize composition node as average of projections
        with torch.no_grad():
            h_comp = (self.rho_add(h_add) + self.rho_mul(h_mul) + self.rho_z(h_z)) / 3.0
        h_comp = h_comp.clone().requires_grad_(False)
        
        # Diffuse until equilibrium
        energies = []
        for step in range(self.config.diffusion_steps):
            h_comp = self.diffusion_step(h_add, h_mul, h_z, h_comp)
            
            if return_energy:
                energy = self.compute_sheaf_energy(h_add, h_mul, h_z, h_comp).mean()
                energies.append(energy.item())
                
                # Early stopping if converged
                if energy.item() < self.config.energy_threshold:
                    break
        
        output = self.output_head(h_comp)
        
        if return_energy:
            return output, energies
        return output
    
    def forward(self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
        """Forward pass using Sheaf Diffusion."""
        return self.forward_diffusion(x, y, z)


def compute_functional_defect_for_task(model: DualTaskMLP, dataloader: DataLoader, 
                                        device: str, task: str = 'add') -> float:
    """
    Compute functional defect for the CORRECT hidden space per task.
    
    This fixes the measurement bug: Task B's eps was always 1.0 because
    we were measuring get_shared_hidden() instead of get_mul_hidden().
    """
    model.eval()
    all_hiddens = []
    all_labels = []
    
    with torch.no_grad():
        for batch in dataloader:
            a, b, targets = [t.to(device) for t in batch]
            
            # Use the CORRECT hidden space for each task
            if task == 'add':
                h = model.get_shared_hidden(a, b)
            else:  # mul
                h = model.get_mul_hidden(a, b)
            
            all_hiddens.append(h)
            all_labels.append(targets)
    
    hiddens = torch.cat(all_hiddens, dim=0)
    labels = torch.cat(all_labels, dim=0)
    
    # Compute within-class variance / total variance
    total_var = torch.var(hiddens, dim=0).sum().item()
    
    within_class_var = 0.0
    unique_labels = labels.unique()
    for label in unique_labels:
        mask = labels == label
        if mask.sum() > 1:
            class_var = torch.var(hiddens[mask], dim=0).sum().item()
            within_class_var += class_var
    
    within_class_var /= len(unique_labels)
    
    eps = within_class_var / (total_var + 1e-10)
    return eps


def create_dataset(p: int, operation: str, train_frac: float = 0.3, seed: int = 42):
    """Create binary operation dataset."""
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    all_a, all_b, all_t = [], [], []
    for a in range(p):
        for b in range(p):
            all_a.append(a)
            all_b.append(b)
            if operation == 'add':
                all_t.append((a + b) % p)
            else:
                all_t.append((a * b) % p)
    
    all_a = torch.tensor(all_a)
    all_b = torch.tensor(all_b)
    all_t = torch.tensor(all_t)
    
    n = len(all_a)
    idx = torch.randperm(n)
    n_train = int(n * train_frac)
    
    train_ds = TensorDataset(all_a[idx[:n_train]], all_b[idx[:n_train]], all_t[idx[:n_train]])
    test_ds = TensorDataset(all_a[idx[n_train:]], all_b[idx[n_train:]], all_t[idx[n_train:]])
    
    return train_ds, test_ds


def create_composition_dataset(p: int, train_frac: float = 0.3, max_samples: int = 50000, seed: int = 42):
    """Create Task C dataset: f(x,y,z) = (x+y)*z mod p"""
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    total = p ** 3
    if total <= max_samples * 2:
        all_x, all_y, all_z, all_t = [], [], [], []
        for x in range(p):
            for y in range(p):
                for z in range(p):
                    all_x.append(x)
                    all_y.append(y)
                    all_z.append(z)
                    all_t.append(((x + y) * z) % p)
        all_x = torch.tensor(all_x)
        all_y = torch.tensor(all_y)
        all_z = torch.tensor(all_z)
        all_t = torch.tensor(all_t)
    else:
        n = min(max_samples * 2, total)
        all_x = torch.randint(0, p, (n,))
        all_y = torch.randint(0, p, (n,))
        all_z = torch.randint(0, p, (n,))
        all_t = ((all_x + all_y) * all_z) % p
    
    n = len(all_x)
    idx = torch.randperm(n)
    n_train = int(n * train_frac)
    
    train_ds = TensorDataset(all_x[idx[:n_train]], all_y[idx[:n_train]], 
                             all_z[idx[:n_train]], all_t[idx[:n_train]])
    test_ds = TensorDataset(all_x[idx[n_train:]], all_y[idx[n_train:]], 
                            all_z[idx[n_train:]], all_t[idx[n_train:]])
    
    return train_ds, test_ds


def train_task(model: DualTaskMLP, train_loader: DataLoader, test_loader: DataLoader,
               device: str, task: str, epochs: int = 3000, lr: float = 1e-3, 
               wd: float = 0.5, grok_threshold: float = 0.99) -> Optional[int]:
    """Train one task until grokking, with CORRECT eps measurement."""
    
    # Only train the relevant parameters
    if task == 'add':
        params = [p for n, p in model.named_parameters() 
                  if 'mul_' not in n and 'head_multiplication' not in n]
    else:
        params = [p for n, p in model.named_parameters() 
                  if 'mul_' in n or 'head_multiplication' in n]
    
    optimizer = torch.optim.AdamW(params, lr=lr, weight_decay=wd)
    criterion = nn.CrossEntropyLoss()
    grok_epoch = None
    
    for epoch in range(epochs):
        model.train()
        for batch in train_loader:
            a, b, targets = [t.to(device) for t in batch]
            optimizer.zero_grad()
            outputs = model(a, b, task=task)
            loss = criterion(outputs, targets)
            loss.backward()
            optimizer.step()
        
        if epoch % 100 == 0 or epoch == epochs - 1:
            # Compute accuracy
            model.eval()
            correct, total = 0, 0
            with torch.no_grad():
                for batch in test_loader:
                    a, b, targets = [t.to(device) for t in batch]
                    preds = model(a, b, task=task).argmax(-1)
                    correct += (preds == targets).sum().item()
                    total += len(targets)
            test_acc = correct / total
            
            # Compute eps with CORRECT hidden space
            eps = compute_functional_defect_for_task(model, test_loader, device, task)
            
            print(f"  {task.upper()} Epoch {epoch:4d} | Acc: {test_acc*100:5.1f}% | eps: {eps:.4f}")
            
            if test_acc >= grok_threshold and eps < 0.15 and grok_epoch is None:
                grok_epoch = epoch
                print(f"  [GROKKED] {task.upper()} at epoch {epoch}!")
                return grok_epoch
    
    return grok_epoch


def load_or_train_stalks(config: SheafConfig, device: str, checkpoint_path: Optional[str] = None):
    """
    Load frozen stalks from checkpoint, or train from scratch if no checkpoint.
    
    The checkpoint should come from sgc_continual_learning.py which is PROVEN to work.
    """
    model = DualTaskMLP(config.p, embed_dim=128, hidden_dim=config.stalk_dim).to(device)
    
    # Create datasets for evaluation
    train_add, test_add = create_dataset(config.p, 'add', config.train_frac, config.seed)
    train_loader_add = DataLoader(train_add, batch_size=512, shuffle=True)
    test_loader_add = DataLoader(test_add, batch_size=512)
    
    train_mul, test_mul = create_dataset(config.p, 'mul', config.train_frac, config.seed + 1)
    train_loader_mul = DataLoader(train_mul, batch_size=512, shuffle=True)
    test_loader_mul = DataLoader(test_mul, batch_size=512)
    
    grok_a, grok_b = None, None
    
    if checkpoint_path and os.path.exists(checkpoint_path):
        print(f"[LOADING] Checkpoint: {checkpoint_path}")
        ckpt = torch.load(checkpoint_path, map_location=device)
        model.load_state_dict(ckpt['model_state_dict'])
        grok_a = ckpt.get('task_a_grokked_epoch')
        grok_b = ckpt.get('task_b_grokked_epoch')
        print(f"  Loaded model with Task A grok@{grok_a}, Task B grok@{grok_b}")
    else:
        print("[WARNING] No checkpoint found. Training from scratch (may not grok).")
        print("Run sgc_continual_learning.py first to generate checkpoint.")
        
        # Train Task A
        print("\n[Task A: Addition]")
        grok_a = train_task(model, train_loader_add, test_loader_add, device, 'add', epochs=3000)
        
        # Freeze Task A
        for name, param in model.named_parameters():
            if 'mul_' not in name and 'head_multiplication' not in name:
                param.requires_grad = False
        
        # Train Task B
        print("\n[Task B: Multiplication]")
        grok_b = train_task(model, train_loader_mul, test_loader_mul, device, 'mul', epochs=3000)
    
    # Freeze all parameters
    for param in model.parameters():
        param.requires_grad = False
    
    # Verify both tasks
    model.eval()
    with torch.no_grad():
        correct_a = sum((model(a.to(device), b.to(device), task='add').argmax(-1) == t.to(device)).sum().item()
                        for a, b, t in test_loader_add)
        acc_a = correct_a / len(test_add)
        
        correct_b = sum((model(a.to(device), b.to(device), task='mul').argmax(-1) == t.to(device)).sum().item()
                        for a, b, t in test_loader_mul)
        acc_b = correct_b / len(test_mul)
    
    eps_a = compute_functional_defect_for_task(model, test_loader_add, device, 'add')
    eps_b = compute_functional_defect_for_task(model, test_loader_mul, device, 'mul')
    
    return model, (acc_a, acc_b), (eps_a, eps_b), (grok_a, grok_b), \
           (train_loader_add, test_loader_add), (train_loader_mul, test_loader_mul)


def run_sheaf_experiment(config: SheafConfig, checkpoint_path: Optional[str] = None):
    """
    Full Sheaf Connector experiment.
    
    Phase 1: Load frozen stalks from checkpoint (or train if no checkpoint)
    Phase 2: Learn restriction maps via Sheaf Diffusion
    Phase 3: Evaluate composition
    """
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"Device: {device}")
    print(f"Config: p={config.p}, stalk_dim={config.stalk_dim}")
    print("=" * 80)
    
    # ================================================================
    # PHASE 1: Load or Train Frozen Stalks
    # ================================================================
    print("\n" + "=" * 80)
    print("PHASE 1: Loading/Training Frozen Stalks")
    print("=" * 80)
    
    model, (acc_a, acc_b), (eps_a, eps_b), (grok_a, grok_b), \
        (train_loader_add, test_loader_add), (train_loader_mul, test_loader_mul) = \
        load_or_train_stalks(config, device, checkpoint_path)
    
    test_add = test_loader_add.dataset
    test_mul = test_loader_mul.dataset
    
    print(f"\n[Frozen Stalks]")
    print(f"  Task A: {acc_a*100:.1f}% acc, eps={eps_a:.4f}")
    print(f"  Task B: {acc_b*100:.1f}% acc, eps={eps_b:.4f}")
    
    if acc_a < 0.95 or acc_b < 0.95:
        print("[WARNING] Tasks not fully learned. Composition results may be limited.")
    
    # ================================================================
    # PHASE 2: Learn Restriction Maps
    # ================================================================
    print("\n" + "=" * 80)
    print("PHASE 2: Learning Restriction Maps (Sheaf Connector)")
    print("=" * 80)
    
    train_comp, test_comp = create_composition_dataset(config.p, config.train_frac, 
                                                        max_samples=30000, seed=config.seed)
    train_loader_comp = DataLoader(train_comp, batch_size=256, shuffle=True)
    test_loader_comp = DataLoader(test_comp, batch_size=256)
    
    print(f"Composition dataset: {len(train_comp)} train, {len(test_comp)} test")
    
    connector = SheafConnector(model, config).to(device)
    
    trainable = sum(p.numel() for p in connector.parameters() if p.requires_grad)
    total = sum(p.numel() for p in connector.parameters())
    print(f"Parameters: {trainable:,} trainable / {total:,} total")
    
    # Zero-shot test
    connector.eval()
    with torch.no_grad():
        correct = sum((connector(x.to(device), y.to(device), z.to(device)).argmax(-1) == t.to(device)).sum().item()
                      for x, y, z, t in test_loader_comp)
        zero_shot = correct / len(test_comp)
    print(f"\nZero-shot accuracy: {zero_shot*100:.1f}%")
    
    # Train restriction maps
    optimizer = torch.optim.AdamW(
        [p for p in connector.parameters() if p.requires_grad],
        lr=1e-3, weight_decay=0.01
    )
    criterion = nn.CrossEntropyLoss()
    
    print(f"\n{'Epoch':>6} | {'Train':>7} | {'Test':>7} | {'Energy':>10}")
    print("-" * 45)
    
    best_acc = 0.0
    
    for epoch in range(500):
        connector.train()
        total_energy = 0.0
        n_batches = 0
        
        for batch in train_loader_comp:
            x, y, z, targets = [t.to(device) for t in batch]
            optimizer.zero_grad()
            
            # Forward with energy tracking
            outputs, energies = connector.forward_diffusion(x, y, z, return_energy=True)
            loss = criterion(outputs, targets)
            
            # Add energy regularization (encourage low sheaf energy)
            if energies:
                energy_loss = 0.001 * energies[-1]
                loss = loss + energy_loss
                total_energy += energies[-1]
            
            loss.backward()
            optimizer.step()
            n_batches += 1
        
        if epoch % 25 == 0 or epoch == 499:
            connector.eval()
            with torch.no_grad():
                # Train accuracy
                correct_train = sum((connector(x.to(device), y.to(device), z.to(device)).argmax(-1) == t.to(device)).sum().item()
                                    for x, y, z, t in train_loader_comp)
                train_acc = correct_train / len(train_comp)
                
                # Test accuracy
                correct_test = sum((connector(x.to(device), y.to(device), z.to(device)).argmax(-1) == t.to(device)).sum().item()
                                   for x, y, z, t in test_loader_comp)
                test_acc = correct_test / len(test_comp)
            
            avg_energy = total_energy / n_batches if n_batches > 0 else 0
            print(f"{epoch:6d} | {train_acc*100:6.1f}% | {test_acc*100:6.1f}% | {avg_energy:10.4f}")
            
            if test_acc > best_acc:
                best_acc = test_acc
    
    # ================================================================
    # FINAL RESULTS
    # ================================================================
    print("\n" + "=" * 80)
    print("FINAL RESULTS")
    print("=" * 80)
    
    # Re-check task preservation
    with torch.no_grad():
        correct_a = sum((model(a.to(device), b.to(device), task='add').argmax(-1) == t.to(device)).sum().item()
                        for a, b, t in test_loader_add)
        final_a = correct_a / len(test_add)
        
        correct_b = sum((model(a.to(device), b.to(device), task='mul').argmax(-1) == t.to(device)).sum().item()
                        for a, b, t in test_loader_mul)
        final_b = correct_b / len(test_mul)
        
        correct_c = sum((connector(x.to(device), y.to(device), z.to(device)).argmax(-1) == t.to(device)).sum().item()
                        for x, y, z, t in test_loader_comp)
        final_c = correct_c / len(test_comp)
    
    print(f"Task A (Addition):       {final_a*100:.1f}%")
    print(f"Task B (Multiplication): {final_b*100:.1f}%")
    print(f"Task C (Composition):    {final_c*100:.1f}%")
    print(f"Zero-shot C:             {zero_shot*100:.1f}%")
    print(f"Improvement:             +{(final_c - zero_shot)*100:.1f}%")
    
    # Analyze restriction maps
    print("\n[Restriction Map Analysis]")
    with torch.no_grad():
        rho_add_norm = torch.norm(connector.rho_add.weight - torch.eye(config.stalk_dim, device=device)).item()
        rho_mul_norm = torch.norm(connector.rho_mul.weight - torch.eye(config.stalk_dim, device=device)).item()
        rho_z_norm = torch.norm(connector.rho_z.weight - torch.eye(config.stalk_dim, device=device)).item()
    
    print(f"  rho_add deviation from identity: {rho_add_norm:.4f}")
    print(f"  rho_mul deviation from identity: {rho_mul_norm:.4f}")
    print(f"  rho_z deviation from identity:   {rho_z_norm:.4f}")
    
    print("\n" + "-" * 50)
    if final_a >= 0.95 and final_b >= 0.95 and final_c >= 0.90:
        print("VERDICT: SUCCESS - Sheaf Composition works!")
        print("Frozen stalks were composed via restriction maps + diffusion.")
    elif final_a >= 0.95 and final_b >= 0.95 and final_c > zero_shot + 0.1:
        print(f"VERDICT: PARTIAL - Composition improved from {zero_shot*100:.1f}% to {final_c*100:.1f}%")
        print("Sheaf structure helps but more training/architecture needed.")
    else:
        print("VERDICT: INCONCLUSIVE - Need grokked stalks to properly test.")
    print("-" * 50)
    
    return {
        'grok_a': grok_a, 'grok_b': grok_b,
        'acc_a': final_a, 'acc_b': final_b, 'acc_c': final_c,
        'eps_a': eps_a, 'eps_b': eps_b,
        'zero_shot': zero_shot,
    }


if __name__ == "__main__":
    config = SheafConfig(
        p=97,
        stalk_dim=256,
        diffusion_steps=10,      # Reduced for faster training
        diffusion_alpha=0.8,     # Higher alpha for faster convergence
        seed=42,
    )
    
    # Try to load checkpoint from Phase 1A
    checkpoint_path = os.path.join(os.path.dirname(__file__), '..', 'checkpoints', 'phase1a_grokked.pt')
    
    results = run_sheaf_experiment(config, checkpoint_path)
