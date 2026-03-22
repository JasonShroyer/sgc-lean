"""
SGC Phase 2: Compositional Generalization Experiment

Tests whether frozen "Functional Blankets" can be composed into higher-order computations.

Architecture:
- Task A (Addition): FROZEN after grokking
- Task B (Multiplication): FROZEN after grokking  
- Task C (Composition): f(x,y,z) = (x + y) * z mod p
  - Only a lightweight "router" is trainable
  - Must read from frozen Task A and Task B representations

Hypothesis: If the Functional Blanket is real, the frozen representations
should be composable with minimal new learning (few-shot).

This tests the "Assembly" part of Predictive Assembly Theory.
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from typing import Dict, List, Tuple, Optional
import numpy as np
from datetime import datetime
import os
import json


class CompositionalMLP(nn.Module):
    """
    MLP for three modular arithmetic tasks with compositional structure.
    
    Architecture:
    - Task A pathway: embed → hidden → head_add (FROZEN after grok)
    - Task B pathway: embed → hidden → head_mul (FROZEN after grok)
    - Task C pathway: ROUTER that reads frozen A and B representations
    
    Task C: f(x,y,z) = (x + y) * z mod p
    
    The router tests whether frozen blankets can be composed.
    """
    
    def __init__(self, p: int, embed_dim: int = 128, hidden_dim: int = 256):
        super().__init__()
        self.p = p
        self.embed_dim = embed_dim
        self.hidden_dim = hidden_dim
        
        # ============================================================
        # Task A Pathway: (a + b) mod p
        # ============================================================
        self.add_embed_a = nn.Embedding(p, embed_dim)
        self.add_embed_b = nn.Embedding(p, embed_dim)
        self.add_fc1 = nn.Linear(embed_dim * 2, hidden_dim)
        self.add_fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.head_addition = nn.Linear(hidden_dim, p)
        
        # ============================================================
        # Task B Pathway: (a * b) mod p
        # ============================================================
        self.mul_embed_a = nn.Embedding(p, embed_dim)
        self.mul_embed_b = nn.Embedding(p, embed_dim)
        self.mul_fc1 = nn.Linear(embed_dim * 2, hidden_dim)
        self.mul_fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.head_multiplication = nn.Linear(hidden_dim, p)
        
        # ============================================================
        # Task C Router: (x + y) * z mod p
        # Reads from frozen Task A and Task B hidden representations
        # ============================================================
        # The router learns to:
        # 1. Compute (x + y) using frozen Task A representation
        # 2. Use that result with z through frozen Task B representation
        # 3. Combine them to produce the final answer
        
        # Embedding for third operand z
        self.comp_embed_z = nn.Embedding(p, embed_dim)
        
        # Router: combines frozen representations
        # Input: Task A hidden (x+y info) + Task B pathway for (*z)
        self.router_fc1 = nn.Linear(hidden_dim * 2, hidden_dim)
        self.router_fc2 = nn.Linear(hidden_dim, hidden_dim)
        self.head_composition = nn.Linear(hidden_dim, p)
    
    # ============================================================
    # Task A Forward (Addition)
    # ============================================================
    def get_add_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get Task A hidden representation."""
        ea = self.add_embed_a(a)
        eb = self.add_embed_b(b)
        x = torch.cat([ea, eb], dim=-1)
        x = F.relu(self.add_fc1(x))
        x = F.relu(self.add_fc2(x))
        return x
    
    def forward_addition(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        h = self.get_add_hidden(a, b)
        return self.head_addition(h)
    
    # ============================================================
    # Task B Forward (Multiplication)
    # ============================================================
    def get_mul_hidden(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        """Get Task B hidden representation."""
        ea = self.mul_embed_a(a)
        eb = self.mul_embed_b(b)
        x = torch.cat([ea, eb], dim=-1)
        x = F.relu(self.mul_fc1(x))
        x = F.relu(self.mul_fc2(x))
        return x
    
    def forward_multiplication(self, a: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
        h = self.get_mul_hidden(a, b)
        return self.head_multiplication(h)
    
    # ============================================================
    # Task C Forward (Composition): (x + y) * z mod p
    # ============================================================
    def forward_composition(self, x: torch.Tensor, y: torch.Tensor, z: torch.Tensor) -> torch.Tensor:
        """
        Compute (x + y) * z mod p using frozen representations.
        
        Strategy:
        1. Get frozen Task A hidden for (x, y) - encodes "x + y" structure
        2. Get embedding for z
        3. Use Task B's multiplication pathway structure with (sum_hidden, z)
        4. Route through lightweight head
        """
        # Get frozen addition representation for (x + y)
        h_add = self.get_add_hidden(x, y)  # Contains (x+y) structure
        
        # Get z embedding and process through mul pathway
        # We treat h_add as if it were a "virtual embedding" for (x+y)
        ez = self.comp_embed_z(z)
        
        # Create a synthetic input for multiplication pathway
        # Project h_add to embed_dim to match ez
        # Actually, let's use a different approach: concatenate h_add with 
        # the multiplication hidden for (placeholder, z)
        
        # Alternative: Use the mul pathway but feed h_add as context
        # Get mul hidden for a dummy multiplication that we'll modulate
        h_mul = self.get_mul_hidden(z, z)  # Gets z's multiplicative structure
        
        # Router combines addition and multiplication representations
        h_combined = torch.cat([h_add, h_mul], dim=-1)
        h_route = F.relu(self.router_fc1(h_combined))
        h_route = F.relu(self.router_fc2(h_route))
        
        return self.head_composition(h_route)
    
    def forward(self, inputs: Tuple, task: str) -> torch.Tensor:
        if task == 'add':
            a, b = inputs
            return self.forward_addition(a, b)
        elif task == 'mul':
            a, b = inputs
            return self.forward_multiplication(a, b)
        elif task == 'comp':
            x, y, z = inputs
            return self.forward_composition(x, y, z)
        else:
            raise ValueError(f"Unknown task: {task}")


def create_composition_dataset(p: int, train_frac: float = 0.3, max_samples: int = 50000, seed: int = 42):
    """
    Create dataset for Task C: f(x,y,z) = (x + y) * z mod p
    
    For large p, we subsample to max_samples to keep training tractable.
    Returns separate datasets for training and testing.
    """
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    total_possible = p ** 3
    
    if total_possible <= max_samples * 2:
        # Small enough - generate all
        all_x = []
        all_y = []
        all_z = []
        all_targets = []
        
        for x in range(p):
            for y in range(p):
                for z in range(p):
                    all_x.append(x)
                    all_y.append(y)
                    all_z.append(z)
                    all_targets.append(((x + y) * z) % p)
        
        all_x = torch.tensor(all_x)
        all_y = torch.tensor(all_y)
        all_z = torch.tensor(all_z)
        all_targets = torch.tensor(all_targets)
    else:
        # Subsample randomly
        n_samples = min(max_samples * 2, total_possible)
        all_x = torch.randint(0, p, (n_samples,))
        all_y = torch.randint(0, p, (n_samples,))
        all_z = torch.randint(0, p, (n_samples,))
        all_targets = ((all_x + all_y) * all_z) % p
    
    # Shuffle and split
    n_total = len(all_x)
    indices = torch.randperm(n_total)
    n_train = int(n_total * train_frac)
    
    train_idx = indices[:n_train]
    test_idx = indices[n_train:]
    
    train_dataset = TensorDataset(
        all_x[train_idx], all_y[train_idx], all_z[train_idx], all_targets[train_idx]
    )
    test_dataset = TensorDataset(
        all_x[test_idx], all_y[test_idx], all_z[test_idx], all_targets[test_idx]
    )
    
    return train_dataset, test_dataset


def create_binary_dataset(p: int, op: str, train_frac: float = 0.3, seed: int = 42):
    """Create dataset for binary operations (add/mul)."""
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    all_a = []
    all_b = []
    all_targets = []
    
    for a in range(p):
        for b in range(p):
            all_a.append(a)
            all_b.append(b)
            if op == 'add':
                all_targets.append((a + b) % p)
            else:
                all_targets.append((a * b) % p)
    
    all_a = torch.tensor(all_a)
    all_b = torch.tensor(all_b)
    all_targets = torch.tensor(all_targets)
    
    n_total = len(all_a)
    indices = torch.randperm(n_total)
    n_train = int(n_total * train_frac)
    
    train_idx = indices[:n_train]
    test_idx = indices[n_train:]
    
    train_dataset = TensorDataset(all_a[train_idx], all_b[train_idx], all_targets[train_idx])
    test_dataset = TensorDataset(all_a[test_idx], all_b[test_idx], all_targets[test_idx])
    
    return train_dataset, test_dataset


def compute_functional_defect(
    model: nn.Module,
    dataloader: DataLoader,
    task: str,
    device: str,
    get_hidden_fn
) -> float:
    """Compute functional defect for a given task."""
    model.eval()
    all_hiddens = []
    all_targets = []
    
    with torch.no_grad():
        for batch in dataloader:
            if task == 'comp':
                x, y, z, targets = [b.to(device) for b in batch]
                h = get_hidden_fn(x, y, z)
            else:
                a, b, targets = [b.to(device) for b in batch]
                h = get_hidden_fn(a, b)
            
            all_hiddens.append(h.cpu())
            all_targets.append(targets.cpu())
    
    hiddens = torch.cat(all_hiddens, dim=0)
    targets = torch.cat(all_targets, dim=0)
    
    # Total variance
    total_var = hiddens.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 1.0
    
    # Within-class variance
    num_classes = model.p
    within_var = 0.0
    count = 0
    
    for c in range(num_classes):
        mask = targets == c
        if mask.sum() > 1:
            class_hiddens = hiddens[mask]
            within_var += class_hiddens.var(dim=0).mean().item()
            count += 1
    
    if count == 0:
        return 1.0
    
    within_var /= count
    return within_var / total_var


def evaluate_accuracy(
    model: nn.Module,
    dataloader: DataLoader,
    task: str,
    device: str
) -> float:
    """Evaluate accuracy for a given task."""
    model.eval()
    correct = 0
    total = 0
    
    with torch.no_grad():
        for batch in dataloader:
            if task == 'comp':
                x, y, z, targets = [b.to(device) for b in batch]
                logits = model.forward_composition(x, y, z)
            elif task == 'add':
                a, b, targets = [b.to(device) for b in batch]
                logits = model.forward_addition(a, b)
            else:
                a, b, targets = [b.to(device) for b in batch]
                logits = model.forward_multiplication(a, b)
            
            preds = logits.argmax(dim=-1)
            correct += (preds == targets).sum().item()
            total += targets.size(0)
    
    return correct / total if total > 0 else 0.0


def freeze_pathway(model: nn.Module, pathway: str):
    """Freeze a specific pathway in the model."""
    frozen = []
    for name, param in model.named_parameters():
        if pathway == 'add' and name.startswith(('add_', 'head_addition')):
            param.requires_grad = False
            frozen.append(name)
        elif pathway == 'mul' and name.startswith(('mul_', 'head_multiplication')):
            param.requires_grad = False
            frozen.append(name)
    return frozen


def run_compositional_experiment(
    p: int = 17,  # Smaller prime for faster Task C (p^3 examples)
    epochs_ab: int = 2000,
    epochs_c: int = 1000,
    lr: float = 1e-3,
    weight_decay: float = 0.5,
    eps_threshold: float = 0.15,
    measure_interval: int = 25,
    seed: int = 42,
):
    """
    Run the compositional generalization experiment.
    
    Phase 1: Train Task A (Addition) until grokked, then freeze
    Phase 2: Train Task B (Multiplication) until grokked, then freeze
    Phase 3: Train Task C (Composition) router with frozen A and B
    """
    torch.manual_seed(seed)
    np.random.seed(seed)
    
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    print(f"\n{'='*100}")
    print(f"SGC PHASE 2: COMPOSITIONAL GENERALIZATION EXPERIMENT")
    print(f"{'='*100}")
    print(f"Task C: f(x,y,z) = (x + y) * z mod {p}")
    print(f"Device: {device}")
    print(f"Total examples for Task C: {p}^3 = {p**3}")
    
    # Create datasets
    add_train, add_test = create_binary_dataset(p, 'add', seed=seed)
    mul_train, mul_test = create_binary_dataset(p, 'mul', seed=seed)
    comp_train, comp_test = create_composition_dataset(p, seed=seed)
    
    add_train_loader = DataLoader(add_train, batch_size=512, shuffle=True)
    add_test_loader = DataLoader(add_test, batch_size=512)
    mul_train_loader = DataLoader(mul_train, batch_size=512, shuffle=True)
    mul_test_loader = DataLoader(mul_test, batch_size=512)
    comp_train_loader = DataLoader(comp_train, batch_size=512, shuffle=True)
    comp_test_loader = DataLoader(comp_test, batch_size=512)
    
    print(f"\nDataset sizes:")
    print(f"  Task A (Add): {len(add_train)} train, {len(add_test)} test")
    print(f"  Task B (Mul): {len(mul_train)} train, {len(mul_test)} test")
    print(f"  Task C (Comp): {len(comp_train)} train, {len(comp_test)} test")
    
    # Create model
    model = CompositionalMLP(p).to(device)
    criterion = nn.CrossEntropyLoss()
    
    # Track metrics
    history = {
        'task_a': {'train_acc': [], 'test_acc': [], 'eps': [], 'epoch': []},
        'task_b': {'train_acc': [], 'test_acc': [], 'eps': [], 'epoch': []},
        'task_c': {'train_acc': [], 'test_acc': [], 'eps': [], 'epoch': []},
    }
    
    # ================================================================
    # PHASE 1: Train Task A (Addition) until grokked
    # ================================================================
    print(f"\n{'-'*100}")
    print("PHASE 1: Training Task A (Addition)")
    print(f"{'-'*100}")
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    task_a_grokked = False
    task_a_grok_epoch = None
    
    for epoch in range(epochs_ab):
        model.train()
        for batch in add_train_loader:
            a, b, targets = [x.to(device) for x in batch]
            optimizer.zero_grad()
            logits = model.forward_addition(a, b)
            loss = criterion(logits, targets)
            loss.backward()
            optimizer.step()
        
        if epoch % measure_interval == 0 or epoch == epochs_ab - 1:
            train_acc = evaluate_accuracy(model, add_train_loader, 'add', device)
            test_acc = evaluate_accuracy(model, add_test_loader, 'add', device)
            
            def get_add_hidden(a, b):
                return model.get_add_hidden(a, b)
            eps = compute_functional_defect(model, add_test_loader, 'add', device, get_add_hidden)
            
            history['task_a']['epoch'].append(epoch)
            history['task_a']['train_acc'].append(train_acc)
            history['task_a']['test_acc'].append(test_acc)
            history['task_a']['eps'].append(eps)
            
            status = ""
            if not task_a_grokked and eps < eps_threshold and test_acc > 0.99:
                task_a_grokked = True
                task_a_grok_epoch = epoch
                status = " <-- GROKKED!"
            
            print(f"  Epoch {epoch:4d} | Train: {train_acc*100:5.1f}% | Test: {test_acc*100:5.1f}% | eps: {eps:.3f}{status}")
            
            if task_a_grokked:
                break
    
    if not task_a_grokked:
        print(f"  [WARNING] Task A did not grok within {epochs_ab} epochs")
    else:
        # Freeze Task A pathway
        frozen_a = freeze_pathway(model, 'add')
        print(f"\n  [FREEZE] Task A pathway frozen ({len(frozen_a)} params)")
    
    # ================================================================
    # PHASE 2: Train Task B (Multiplication) until grokked
    # ================================================================
    print(f"\n{'-'*100}")
    print("PHASE 2: Training Task B (Multiplication)")
    print(f"{'-'*100}")
    
    # New optimizer for unfrozen params only
    optimizer = torch.optim.AdamW(
        [p for p in model.parameters() if p.requires_grad],
        lr=lr, weight_decay=weight_decay
    )
    
    task_b_grokked = False
    task_b_grok_epoch = None
    
    for epoch in range(epochs_ab):
        model.train()
        for batch in mul_train_loader:
            a, b, targets = [x.to(device) for x in batch]
            optimizer.zero_grad()
            logits = model.forward_multiplication(a, b)
            loss = criterion(logits, targets)
            loss.backward()
            optimizer.step()
        
        if epoch % measure_interval == 0 or epoch == epochs_ab - 1:
            # Check Task A is still frozen
            task_a_test_acc = evaluate_accuracy(model, add_test_loader, 'add', device)
            
            train_acc = evaluate_accuracy(model, mul_train_loader, 'mul', device)
            test_acc = evaluate_accuracy(model, mul_test_loader, 'mul', device)
            
            def get_mul_hidden(a, b):
                return model.get_mul_hidden(a, b)
            eps = compute_functional_defect(model, mul_test_loader, 'mul', device, get_mul_hidden)
            
            history['task_b']['epoch'].append(epoch)
            history['task_b']['train_acc'].append(train_acc)
            history['task_b']['test_acc'].append(test_acc)
            history['task_b']['eps'].append(eps)
            
            status = ""
            if not task_b_grokked and eps < eps_threshold and test_acc > 0.99:
                task_b_grokked = True
                task_b_grok_epoch = epoch
                status = " <-- GROKKED!"
            
            print(f"  Epoch {epoch:4d} | Train: {train_acc*100:5.1f}% | Test: {test_acc*100:5.1f}% | eps: {eps:.3f} | A preserved: {task_a_test_acc*100:.1f}%{status}")
            
            if task_b_grokked:
                break
    
    if not task_b_grokked:
        print(f"  [WARNING] Task B did not grok within {epochs_ab} epochs")
    else:
        # Freeze Task B pathway
        frozen_b = freeze_pathway(model, 'mul')
        print(f"\n  [FREEZE] Task B pathway frozen ({len(frozen_b)} params)")
    
    # ================================================================
    # PHASE 3: Train Task C (Composition) - THE KEY TEST
    # ================================================================
    print(f"\n{'-'*100}")
    print("PHASE 3: Training Task C (Composition) - ROUTER ONLY")
    print(f"Task C: f(x,y,z) = (x + y) * z mod {p}")
    print(f"Hypothesis: Frozen blankets should be composable")
    print(f"{'-'*100}")
    
    # Count trainable parameters
    trainable_params = sum(p.numel() for p in model.parameters() if p.requires_grad)
    total_params = sum(p.numel() for p in model.parameters())
    print(f"\n  Trainable: {trainable_params:,} / {total_params:,} params ({100*trainable_params/total_params:.1f}%)")
    
    # List trainable components
    print("  Trainable components:")
    for name, param in model.named_parameters():
        if param.requires_grad:
            print(f"    - {name}: {param.numel()} params")
    
    # New optimizer for router only
    optimizer = torch.optim.AdamW(
        [p for p in model.parameters() if p.requires_grad],
        lr=lr, weight_decay=weight_decay
    )
    
    # Check zero-shot performance first!
    zero_shot_acc = evaluate_accuracy(model, comp_test_loader, 'comp', device)
    print(f"\n  ZERO-SHOT Test Accuracy: {zero_shot_acc*100:.1f}%")
    
    task_c_grokked = False
    task_c_grok_epoch = None
    
    print(f"\n  {'Epoch':>6} | {'Train':>7} | {'Test':>7} | {'eps':>6} | {'A':>5} | {'B':>5}")
    print(f"  {'-'*50}")
    
    for epoch in range(epochs_c):
        model.train()
        for batch in comp_train_loader:
            x, y, z, targets = [t.to(device) for t in batch]
            optimizer.zero_grad()
            logits = model.forward_composition(x, y, z)
            loss = criterion(logits, targets)
            loss.backward()
            optimizer.step()
        
        if epoch % measure_interval == 0 or epoch == epochs_c - 1:
            # Verify Task A and B are preserved
            task_a_test_acc = evaluate_accuracy(model, add_test_loader, 'add', device)
            task_b_test_acc = evaluate_accuracy(model, mul_test_loader, 'mul', device)
            
            train_acc = evaluate_accuracy(model, comp_train_loader, 'comp', device)
            test_acc = evaluate_accuracy(model, comp_test_loader, 'comp', device)
            
            # For Task C, get the router hidden
            def get_comp_hidden(x, y, z):
                h_add = model.get_add_hidden(x, y)
                h_mul = model.get_mul_hidden(z, z)
                h_combined = torch.cat([h_add, h_mul], dim=-1)
                h_route = F.relu(model.router_fc1(h_combined))
                return F.relu(model.router_fc2(h_route))
            
            eps = compute_functional_defect(model, comp_test_loader, 'comp', device, get_comp_hidden)
            
            history['task_c']['epoch'].append(epoch)
            history['task_c']['train_acc'].append(train_acc)
            history['task_c']['test_acc'].append(test_acc)
            history['task_c']['eps'].append(eps)
            
            status = ""
            if not task_c_grokked and test_acc > 0.99:
                task_c_grokked = True
                task_c_grok_epoch = epoch
                status = " <-- GROKKED!"
            
            print(f"  {epoch:6d} | {train_acc*100:6.1f}% | {test_acc*100:6.1f}% | {eps:.4f} | {task_a_test_acc*100:4.1f}% | {task_b_test_acc*100:4.1f}%{status}")
    
    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'='*100}")
    print("EXPERIMENT SUMMARY")
    print(f"{'='*100}")
    
    final_a_acc = evaluate_accuracy(model, add_test_loader, 'add', device)
    final_b_acc = evaluate_accuracy(model, mul_test_loader, 'mul', device)
    final_c_acc = evaluate_accuracy(model, comp_test_loader, 'comp', device)
    
    print(f"\nTask A (Addition): {final_a_acc*100:.1f}% (grokked at epoch {task_a_grok_epoch})")
    print(f"Task B (Multiplication): {final_b_acc*100:.1f}% (grokked at epoch {task_b_grok_epoch})")
    print(f"Task C (Composition): {final_c_acc*100:.1f}% (grokked at epoch {task_c_grok_epoch})")
    print(f"Zero-shot C accuracy: {zero_shot_acc*100:.1f}%")
    
    print(f"\n{'-'*50}")
    if final_a_acc > 0.99 and final_b_acc > 0.99 and final_c_acc > 0.99:
        print("VERDICT: SUCCESS - Frozen blankets are COMPOSABLE!")
        if zero_shot_acc > 0.5:
            print("         BONUS: Significant zero-shot transfer!")
    elif final_a_acc > 0.99 and final_b_acc > 0.99:
        print(f"VERDICT: PARTIAL - A and B preserved, but C only reached {final_c_acc*100:.1f}%")
    else:
        print("VERDICT: FAILURE - Memory protection failed")
    print(f"{'-'*50}")
    
    return history, model


if __name__ == "__main__":
    history, model = run_compositional_experiment(
        p=59,  # Medium prime - large enough to grok, small enough to be fast
        epochs_ab=2000,
        epochs_c=2000,
        lr=1e-3,
        weight_decay=0.5,
        eps_threshold=0.15,
        measure_interval=50,
        seed=42,
    )
