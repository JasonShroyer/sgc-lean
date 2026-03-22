#!/usr/bin/env python3
"""
SGC Emergence Experiment v2: Autopoietic Crystal Growth
========================================================

Demonstrates the SGC Theory of Emergence: neural networks that GROW
when the current topology is insufficient for new tasks.

Key Innovation: Mitotic Controller triggers growth based on
ThermodynamicFrustration = Defect x Temperature

Run with: python demos/sgc_emergence_experiment_v2.py

Author: SGC Research Team
Date: February 5, 2026
"""

import sys
import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
import numpy as np
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
from enum import Enum


# Force unbuffered output for real-time progress
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


# =============================================================================
# CONFIGURATION
# =============================================================================

@dataclass
class Config:
    p: int = 97                      # Prime for modular arithmetic
    embed_dim: int = 64              # Smaller for faster training
    hidden_dim: int = 64
    n_layers: int = 1
    
    phase1_epochs: int = 500         # Grokking Task A
    phase2_epochs: int = 100         # Frustration detection
    phase3_epochs: int = 500         # Symbiosis learning
    
    lr: float = 1e-3
    weight_decay: float = 1.0
    batch_size: int = 512
    
    grokking_threshold: float = 0.15
    frustration_critical: float = 0.3
    max_temperature: float = 0.2
    
    device: str = 'cuda' if torch.cuda.is_available() else 'cpu'
    seed: int = 42


# =============================================================================
# SIMPLE MODEL
# =============================================================================

class SimpleLobe(nn.Module):
    """Single lobe with hidden layers and output head."""
    
    def __init__(self, input_dim: int, hidden_dim: int, output_dim: int):
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(input_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU()
        )
        self.head = nn.Linear(hidden_dim, output_dim)
        self._init()
    
    def _init(self):
        for m in self.modules():
            if isinstance(m, nn.Linear):
                nn.init.xavier_uniform_(m.weight)
                if m.bias is not None:
                    nn.init.zeros_(m.bias)
    
    def get_hidden(self, x):
        return self.net(x)
    
    def forward(self, x, noise=0.0):
        h = self.net(x)
        if noise > 0 and self.training:
            h = h + torch.randn_like(h) * noise
        return self.head(h)


class AutopoieticNet(nn.Module):
    """Network that can grow new lobes via mitosis."""
    
    def __init__(self, cfg: Config):
        super().__init__()
        self.cfg = cfg
        
        # Shared embeddings
        self.embed_a = nn.Embedding(cfg.p, cfg.embed_dim)
        self.embed_b = nn.Embedding(cfg.p, cfg.embed_dim)
        nn.init.normal_(self.embed_a.weight, std=0.02)
        nn.init.normal_(self.embed_b.weight, std=0.02)
        
        # Lobes
        self.lobes = nn.ModuleList()
        self.bridges = nn.ModuleList()
        self.frozen = []
        
        # Create first lobe
        self.lobes.append(SimpleLobe(cfg.embed_dim * 2, cfg.hidden_dim, cfg.p))
        self.frozen.append(False)
    
    def get_embed(self, a, b):
        return torch.cat([self.embed_a(a), self.embed_b(b)], dim=-1)
    
    def forward_lobe(self, lobe_id: int, a, b, noise=0.0):
        emb = self.get_embed(a, b)
        
        if lobe_id == 0:
            return self.lobes[0](emb, noise)
        else:
            # Get parent hidden (frozen)
            with torch.no_grad():
                parent_h = self.lobes[lobe_id - 1].get_hidden(
                    self.get_embed(a, b) if lobe_id == 1 else self._get_full_input(lobe_id - 1, a, b)
                )
            bridged = self.bridges[lobe_id - 1](parent_h)
            combined = torch.cat([emb, bridged], dim=-1)
            return self.lobes[lobe_id](combined, noise)
    
    def get_hidden(self, lobe_id: int, a, b):
        emb = self.get_embed(a, b)
        if lobe_id == 0:
            return self.lobes[0].get_hidden(emb)
        else:
            with torch.no_grad():
                parent_h = self.lobes[lobe_id - 1].get_hidden(self.get_embed(a, b))
            bridged = self.bridges[lobe_id - 1](parent_h)
            combined = torch.cat([emb, bridged], dim=-1)
            return self.lobes[lobe_id].get_hidden(combined)
    
    def trigger_mitosis(self):
        """Spawn a new lobe, freeze the old one."""
        device = next(self.parameters()).device
        
        # Freeze current lobe
        parent_id = len(self.lobes) - 1
        self.frozen[parent_id] = True
        for p in self.lobes[parent_id].parameters():
            p.requires_grad = False
        
        # Create bridge
        bridge = nn.Linear(self.cfg.hidden_dim, self.cfg.hidden_dim, bias=False)
        nn.init.eye_(bridge.weight)
        bridge = bridge.to(device)
        self.bridges.append(bridge)
        
        # Create new lobe
        input_dim = self.cfg.embed_dim * 2 + self.cfg.hidden_dim
        new_lobe = SimpleLobe(input_dim, self.cfg.hidden_dim, self.cfg.p)
        new_lobe = new_lobe.to(device)
        self.lobes.append(new_lobe)
        self.frozen.append(False)
        
        return len(self.lobes) - 1
    
    def trainable_params(self):
        params = list(self.embed_a.parameters()) + list(self.embed_b.parameters())
        for i, lobe in enumerate(self.lobes):
            if not self.frozen[i]:
                params.extend(lobe.parameters())
        for bridge in self.bridges:
            params.extend(bridge.parameters())
        return params


# =============================================================================
# DATASETS
# =============================================================================

def make_addition_data(p, train_frac=0.5):
    pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.shuffle(pairs)
    split = int(len(pairs) * train_frac)
    
    def tensors(ps):
        a = torch.tensor([x[0] for x in ps], dtype=torch.long)
        b = torch.tensor([x[1] for x in ps], dtype=torch.long)
        c = torch.tensor([(x[0] + x[1]) % p for x in ps], dtype=torch.long)
        return a, b, c
    
    return tensors(pairs[:split]), tensors(pairs[split:])


def make_mult_data(p, train_frac=0.5):
    pairs = [(a, b) for a in range(p) for b in range(p)]
    np.random.shuffle(pairs)
    split = int(len(pairs) * train_frac)
    
    def tensors(ps):
        a = torch.tensor([x[0] for x in ps], dtype=torch.long)
        b = torch.tensor([x[1] for x in ps], dtype=torch.long)
        c = torch.tensor([(x[0] * x[1]) % p for x in ps], dtype=torch.long)
        return a, b, c
    
    return tensors(pairs[:split]), tensors(pairs[split:])


# =============================================================================
# FUNCTIONAL DEFECT
# =============================================================================

def compute_defect(model, lobe_id, loader, p, device):
    """Compute functional defect = within-class variance / total variance."""
    model.eval()
    all_h, all_t = [], []
    
    with torch.no_grad():
        for batch in loader:
            a, b, c = [x.to(device) for x in batch]
            h = model.get_hidden(lobe_id, a, b)
            all_h.append(h)
            all_t.append(c)
    
    H = torch.cat(all_h, dim=0)
    T = torch.cat(all_t, dim=0)
    
    total_var = H.var(dim=0).mean().item()
    if total_var < 1e-10:
        return 0.0
    
    within_vars = []
    for c in range(p):
        mask = (T == c)
        if mask.sum() > 1:
            within_vars.append(H[mask].var(dim=0).mean().item())
    
    if not within_vars:
        return 1.0
    
    within_var = np.mean(within_vars)
    return within_var / (total_var + 1e-10)


# =============================================================================
# TRAINING PHASES
# =============================================================================

def phase1_crystallize(model, cfg):
    """Phase 1: Grok Task A (addition)."""
    print("\n" + "=" * 70)
    print("PHASE 1: CRYSTALLIZE - Grokking Task A (Addition)")
    print("=" * 70)
    
    (tr_a, tr_b, tr_c), (te_a, te_b, te_c) = make_addition_data(cfg.p)
    train_ds = TensorDataset(tr_a, tr_b, tr_c)
    test_ds = TensorDataset(te_a, te_b, te_c)
    train_ld = DataLoader(train_ds, batch_size=cfg.batch_size, shuffle=True)
    test_ld = DataLoader(test_ds, batch_size=cfg.batch_size)
    
    opt = torch.optim.AdamW(model.parameters(), lr=cfg.lr, weight_decay=cfg.weight_decay)
    crit = nn.CrossEntropyLoss()
    
    print(f"{'Ep':>5} | {'Train':>6} | {'Test':>6} | {'Defect':>8} | Status")
    print("-" * 50)
    
    for epoch in range(1, cfg.phase1_epochs + 1):
        # Train
        model.train()
        correct, total = 0, 0
        for a, b, c in train_ld:
            a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
            opt.zero_grad()
            out = model.forward_lobe(0, a, b)
            loss = crit(out, c)
            loss.backward()
            opt.step()
            correct += (out.argmax(1) == c).sum().item()
            total += len(a)
        train_acc = correct / total
        
        # Test
        model.eval()
        correct, total = 0, 0
        with torch.no_grad():
            for a, b, c in test_ld:
                a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
                out = model.forward_lobe(0, a, b)
                correct += (out.argmax(1) == c).sum().item()
                total += len(a)
        test_acc = correct / total
        
        # Defect (every 10 epochs)
        if epoch % 10 == 0 or epoch == 1:
            defect = compute_defect(model, 0, train_ld, cfg.p, cfg.device)
            
            if defect > 0.5:
                status = "MEMORIZING"
            elif defect > cfg.grokking_threshold:
                status = "TRANSITION"
            else:
                status = "GROKKED!"
            
            print(f"{epoch:5d} | {train_acc:6.1%} | {test_acc:6.1%} | {defect:8.4f} | {status}")
            
            if defect < cfg.grokking_threshold and test_acc > 0.95:
                print(f"\n*** PHASE 1 COMPLETE: Task A crystallized! ***")
                return defect, train_ld
    
    defect = compute_defect(model, 0, train_ld, cfg.p, cfg.device)
    print(f"\n*** PHASE 1 TIMEOUT ***")
    return defect, train_ld


def phase2_frustrate(model, cfg, task_a_ld):
    """Phase 2: Attempt Task B in same lobe - watch frustration rise."""
    print("\n" + "=" * 70)
    print("PHASE 2: FRUSTRATE - Attempting Task B in Same Manifold")
    print("=" * 70)
    print("Watching: Task A accuracy should DROP (catastrophic forgetting)")
    
    (tr_a, tr_b, tr_c), _ = make_mult_data(cfg.p)
    train_ds = TensorDataset(tr_a, tr_b, tr_c)
    train_ld = DataLoader(train_ds, batch_size=cfg.batch_size, shuffle=True)
    
    opt = torch.optim.AdamW(model.parameters(), lr=cfg.lr, weight_decay=0.5)
    crit = nn.CrossEntropyLoss()
    
    print(f"{'Ep':>5} | {'A_Acc':>6} | {'B_Acc':>6} | {'Defect':>8} | {'Temp':>6} | {'Frust':>8}")
    print("-" * 65)
    
    temperature = 0.0
    
    for epoch in range(1, cfg.phase2_epochs + 1):
        # Train on Task B (in lobe 0!)
        model.train()
        correct_b, total_b = 0, 0
        for a, b, c in train_ld:
            a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
            opt.zero_grad()
            out = model.forward_lobe(0, a, b, noise=temperature)
            loss = crit(out, c)
            loss.backward()
            opt.step()
            correct_b += (out.argmax(1) == c).sum().item()
            total_b += len(a)
        acc_b = correct_b / total_b
        
        # Evaluate Task A
        model.eval()
        correct_a, total_a = 0, 0
        with torch.no_grad():
            for a, b, c in task_a_ld:
                a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
                out = model.forward_lobe(0, a, b)
                correct_a += (out.argmax(1) == c).sum().item()
                total_a += len(a)
        acc_a = correct_a / total_a
        
        # Defect and frustration
        defect = compute_defect(model, 0, train_ld, cfg.p, cfg.device)
        temperature = min(cfg.max_temperature, temperature + 0.01)
        frustration = defect * temperature
        
        print(f"{epoch:5d} | {acc_a:6.1%} | {acc_b:6.1%} | {defect:8.4f} | {temperature:6.3f} | {frustration:8.4f}")
        
        # Check mitosis trigger
        if frustration > cfg.frustration_critical and temperature >= cfg.max_temperature:
            print(f"\n*** MITOSIS TRIGGERED! Frustration = {frustration:.4f} ***")
            return True, epoch
    
    print(f"\n*** PHASE 2 COMPLETE: Forcing mitosis for demonstration ***")
    return False, cfg.phase2_epochs


def phase3_symbiosis(model, cfg, task_a_ld):
    """Phase 3: Learn Task B in new lobe while Task A is protected."""
    print("\n" + "=" * 70)
    print("PHASE 3: SYMBIOSIS - Learning Task B in New Lobe")
    print("=" * 70)
    print(f"Network: {len(model.lobes)} lobes | Lobe 0: FROZEN | Lobe 1: LEARNING")
    
    new_lobe = len(model.lobes) - 1
    
    (tr_a, tr_b, tr_c), (te_a, te_b, te_c) = make_mult_data(cfg.p)
    train_ds = TensorDataset(tr_a, tr_b, tr_c)
    test_ds = TensorDataset(te_a, te_b, te_c)
    train_ld = DataLoader(train_ds, batch_size=cfg.batch_size, shuffle=True)
    test_ld = DataLoader(test_ds, batch_size=cfg.batch_size)
    
    opt = torch.optim.AdamW(model.trainable_params(), lr=cfg.lr, weight_decay=0.5)
    crit = nn.CrossEntropyLoss()
    
    print(f"{'Ep':>5} | {'A_Acc':>6} | {'B_Train':>7} | {'B_Test':>6} | {'A_Def':>7} | {'B_Def':>7} | Status")
    print("-" * 75)
    
    for epoch in range(1, cfg.phase3_epochs + 1):
        # Train new lobe on Task B
        model.train()
        correct_b, total_b = 0, 0
        for a, b, c in train_ld:
            a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
            opt.zero_grad()
            out = model.forward_lobe(new_lobe, a, b)
            loss = crit(out, c)
            loss.backward()
            opt.step()
            correct_b += (out.argmax(1) == c).sum().item()
            total_b += len(a)
        train_acc_b = correct_b / total_b
        
        # Test Task B
        model.eval()
        correct, total = 0, 0
        with torch.no_grad():
            for a, b, c in test_ld:
                a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
                out = model.forward_lobe(new_lobe, a, b)
                correct += (out.argmax(1) == c).sum().item()
                total += len(a)
        test_acc_b = correct / total
        
        # Task A (through frozen lobe 0)
        correct_a, total_a = 0, 0
        with torch.no_grad():
            for a, b, c in task_a_ld:
                a, b, c = a.to(cfg.device), b.to(cfg.device), c.to(cfg.device)
                out = model.forward_lobe(0, a, b)
                correct_a += (out.argmax(1) == c).sum().item()
                total_a += len(a)
        acc_a = correct_a / total_a
        
        # Print every 10 epochs
        if epoch % 10 == 0 or epoch == 1:
            def_a = compute_defect(model, 0, task_a_ld, cfg.p, cfg.device)
            def_b = compute_defect(model, new_lobe, train_ld, cfg.p, cfg.device)
            
            if test_acc_b > 0.95 and acc_a > 0.95:
                status = "BOTH OK!"
            elif acc_a < 0.90:
                status = "A FORGOT!"
            elif test_acc_b > 0.95:
                status = "B GROKKED"
            else:
                status = "LEARNING"
            
            print(f"{epoch:5d} | {acc_a:6.1%} | {train_acc_b:7.1%} | {test_acc_b:6.1%} | {def_a:7.4f} | {def_b:7.4f} | {status}")
            
            if test_acc_b > 0.95 and acc_a > 0.95:
                print(f"\n*** PHASE 3 COMPLETE: Both tasks grokked! ***")
                return {'acc_a': acc_a, 'acc_b': test_acc_b, 'def_a': def_a, 'def_b': def_b}
    
    def_a = compute_defect(model, 0, task_a_ld, cfg.p, cfg.device)
    def_b = compute_defect(model, new_lobe, train_ld, cfg.p, cfg.device)
    return {'acc_a': acc_a, 'acc_b': test_acc_b, 'def_a': def_a, 'def_b': def_b}


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("\n" + "=" * 70)
    print("   SGC EMERGENCE EXPERIMENT: AUTOPOIETIC CRYSTAL GROWTH")
    print("=" * 70)
    print("""
    Hypothesis: Networks can exhibit UNLIMITED continual learning
    by GROWING new lobes when the current topology is insufficient.
    
    Phase 1: Grok Task A (addition) - crystallize algebraic structure
    Phase 2: Attempt Task B (mult) in same lobe - watch forgetting
    Phase 3: Trigger MITOSIS, learn Task B in new lobe - zero forgetting
    """)
    print("=" * 70)
    
    cfg = Config()
    torch.manual_seed(cfg.seed)
    np.random.seed(cfg.seed)
    
    print(f"Config: p={cfg.p}, hidden={cfg.hidden_dim}, device={cfg.device}")
    
    # Create model
    model = AutopoieticNet(cfg).to(cfg.device)
    print(f"Initial network: {len(model.lobes)} lobe(s)")
    
    # Phase 1: Crystallize
    baseline_defect, task_a_ld = phase1_crystallize(model, cfg)
    
    # Phase 2: Frustrate (demonstrate catastrophic forgetting)
    triggered, epochs = phase2_frustrate(model, cfg, task_a_ld)
    
    # Trigger mitosis
    print("\n*** TRIGGERING MITOSIS ***")
    new_lobe_id = model.trigger_mitosis()
    print(f"    Lobe 0: FROZEN")
    print(f"    Lobe {new_lobe_id}: CREATED (connected via bridge)")
    
    # Phase 3: Symbiosis
    results = phase3_symbiosis(model, cfg, task_a_ld)
    
    # Summary
    print("\n" + "=" * 70)
    print("                    EXPERIMENT SUMMARY")
    print("=" * 70)
    print(f"\nNetwork: {len(model.lobes)} lobes")
    print(f"  Lobe 0 (Task A): {'FROZEN' if model.frozen[0] else 'ACTIVE'}")
    print(f"  Lobe 1 (Task B): {'FROZEN' if model.frozen[1] else 'ACTIVE'}")
    
    print(f"\nResults:")
    print(f"  Task A Accuracy: {results['acc_a']:.1%}")
    print(f"  Task B Accuracy: {results['acc_b']:.1%}")
    print(f"  Task A Defect:   {results['def_a']:.4f}")
    print(f"  Task B Defect:   {results['def_b']:.4f}")
    
    # Success check
    success = results['acc_a'] > 0.95 and results['acc_b'] > 0.95
    
    print("\n" + "=" * 70)
    if success:
        print("   SUCCESS: ZERO-FORGETTING CONTINUAL LEARNING ACHIEVED!")
        print("")
        print("   The network learned TWO tasks without catastrophic forgetting")
        print("   by GROWING a new lobe when the first was full.")
    else:
        print("   INCOMPLETE: Further tuning needed")
    print("=" * 70 + "\n")
    
    return success


if __name__ == "__main__":
    main()
