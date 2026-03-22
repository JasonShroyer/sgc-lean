"""
Adaptive Polarity v6.2: Correctness-Aware Homeostat

KEY FIX from v6.1:
- v6.1 achieved 65.9% with working write/erase/crystallize mechanics
- But accuracy below v5's 85% because homeostat commits based only on CONFLICT
- This version adds CORRECTNESS signal during training

THE PHYSICS:
- Conflict = topology violation (neighbor overlap) - UNSUPERVISED
- Correctness = match with solution - SUPERVISED (training only)
- Alpha grows when BOTH low conflict AND high correctness probability
- This teaches the network to be confident only when actually correct

During inference: only conflict is used (no solution available)
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
class Config:
    stalk_dim: int = 64
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    
    # Confidence dynamics
    eta_growth: float = 0.3
    delta_decay: float = 0.35
    crystallize_threshold: float = 0.8
    evaporate_threshold: float = 0.0
    
    # Thresholds
    low_conflict: float = 0.15
    high_conflict: float = 0.35
    write_threshold: float = 0.5
    
    max_cycles: int = 6
    polarity_init: float = -0.5
    
    epochs: int = 200
    batch_size: int = 32
    lr: float = 1e-3
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_v6_2"


def build_graph():
    edges, types = [], {'row': [], 'col': [], 'box': []}
    idx = 0
    for r in range(9):
        for c1 in range(9):
            for c2 in range(c1+1, 9):
                edges.append((r*9+c1, r*9+c2))
                types['row'].append(idx)
                idx += 1
    for c in range(9):
        for r1 in range(9):
            for r2 in range(r1+1, 9):
                edges.append((r1*9+c, r2*9+c))
                types['col'].append(idx)
                idx += 1
    for br in range(3):
        for bc in range(3):
            cells = [(br*3+dr)*9+bc*3+dc for dr in range(3) for dc in range(3)]
            for i in range(len(cells)):
                for j in range(i+1, len(cells)):
                    edges.append((cells[i], cells[j]))
                    types['box'].append(idx)
                    idx += 1
    return edges, types


class State:
    def __init__(self, puzzles, solutions=None):
        B = puzzles.shape[0]
        dev = puzzles.device
        self.pen = puzzles.clone()
        self.pencil = torch.zeros_like(puzzles)
        self.alpha = torch.zeros(B, 81, device=dev)
        self.solutions = solutions  # For correctness signal during training
    
    def board(self):
        b = self.pen.clone()
        m = (self.pen == 0) & (self.pencil > 0)
        b[m] = self.pencil[m]
        return b
    
    def fixed(self):
        return (self.pen > 0) | ((self.pencil > 0) & (self.alpha > 0.5))


class Diffusion(nn.Module):
    def __init__(self, edges, types, dim, pol_init):
        super().__init__()
        self.dim = dim
        src = torch.tensor([e[0] for e in edges])
        dst = torch.tensor([e[1] for e in edges])
        self.register_buffer('src', src)
        self.register_buffer('dst', dst)
        
        tidx = torch.zeros(len(edges), dtype=torch.long)
        for t, (_, idxs) in enumerate(types.items()):
            for i in idxs:
                tidx[i] = t
        self.register_buffer('tidx', tidx)
        
        self.W = nn.ParameterList([nn.Parameter(torch.eye(dim) + 0.1*torch.randn(dim,dim)) for _ in range(3)])
        self.pol = nn.Parameter(torch.ones(3) * pol_init)
    
    def g(self):
        return torch.sigmoid(self.pol)
    
    def conflict(self, logits):
        p = F.softmax(logits, -1)
        B = p.shape[0]
        ov = (p[:,self.src] * p[:,self.dst]).sum(-1)
        c = torch.zeros(B, 81, device=logits.device)
        c.scatter_add_(1, self.src.unsqueeze(0).expand(B,-1), ov)
        c.scatter_add_(1, self.dst.unsqueeze(0).expand(B,-1), ov)
        return c / 20.0
    
    def energy(self, logits):
        p = F.softmax(logits, -1)
        return (p[:,self.src] * p[:,self.dst]).sum(-1).mean()
    
    def step(self, s, logits, dt, fixed):
        B, N, D = s.shape
        p = F.softmax(logits, -1)
        g = self.g()[self.tidx].view(1,-1,1)
        ov = (p[:,self.src] * p[:,self.dst]).sum(-1, keepdim=True)
        diff = s[:,self.src] - s[:,self.dst]
        flow = g * diff + (1-g) * (-ov * diff)
        drift = torch.zeros_like(s)
        drift.scatter_add_(1, self.dst.view(1,-1,1).expand(B,-1,D), dt*flow)
        drift.scatter_add_(1, self.src.view(1,-1,1).expand(B,-1,D), -dt*flow)
        new = s + drift
        return torch.where(fixed.unsqueeze(-1), s, new)


class Homeostat(nn.Module):
    def __init__(self, cfg, edges, types):
        super().__init__()
        self.cfg = cfg
        self.embed = nn.Embedding(10, cfg.stalk_dim)
        self.mlp = nn.Sequential(
            nn.Linear(cfg.stalk_dim, cfg.stalk_dim*2),
            nn.ReLU(),
            nn.Linear(cfg.stalk_dim*2, cfg.stalk_dim)
        )
        self.diff = Diffusion(edges, types, cfg.stalk_dim, cfg.polarity_init)
        self.head = nn.Linear(cfg.stalk_dim, 9)
    
    def sense(self, state):
        cfg = self.cfg
        s = self.embed(state.board())
        s = s + self.mlp(s)
        fixed = state.fixed()
        for _ in range(cfg.diffusion_steps):
            logits = self.head(s)
            s = self.diff.step(s, logits, cfg.diffusion_dt, fixed)
            s = s + 0.1 * self.mlp(s)
        logits = self.head(s)
        conflict = self.diff.conflict(logits)
        entropy = -(F.softmax(logits,-1) * F.log_softmax(logits,-1)).sum(-1)
        return logits, conflict, entropy
    
    def act(self, state, logits, conflict, entropy, training=True):
        cfg = self.cfg
        stats = {'written': 0, 'evaporated': 0, 'crystallized': 0}
        
        probs = F.softmax(logits, -1)
        max_p, best = probs.max(-1)
        best = best + 1
        
        has_pencil = (state.pencil > 0)
        certainty = 1.0 - entropy / 2.2
        
        # === CORRECTNESS SIGNAL (training only) ===
        if training and state.solutions is not None:
            # Check if pencil matches solution
            pencil_correct = (state.pencil - 1 == state.solutions) & has_pencil
            pencil_wrong = (state.pencil - 1 != state.solutions) & has_pencil
            
            # Correct + low conflict + certain -> grow fast
            good = pencil_correct & (conflict < cfg.low_conflict) & (certainty > 0.4)
            state.alpha[good] += cfg.eta_growth
            
            # Correct but conflicted -> grow slow
            ok = pencil_correct & ~good
            state.alpha[ok] += cfg.eta_growth * 0.2
            
            # Wrong -> decay (learn to not be confident when wrong)
            state.alpha[pencil_wrong] -= cfg.delta_decay
        else:
            # Inference: use conflict + certainty only
            good = (conflict < cfg.low_conflict) & (certainty > 0.4) & has_pencil
            state.alpha[good] += cfg.eta_growth
            ok = ~good & (conflict < cfg.high_conflict) & (certainty > 0.3) & has_pencil
            state.alpha[ok] += cfg.eta_growth * 0.3
            bad = ((conflict > cfg.high_conflict) | (certainty < 0.25)) & has_pencil
            state.alpha[bad] -= cfg.delta_decay
        
        state.alpha = torch.clamp(state.alpha, -0.5, 1.0)
        
        # Evaporate
        evap = (state.alpha < cfg.evaporate_threshold) & has_pencil
        if evap.any():
            state.pencil[evap] = 0
            state.alpha[evap] = 0
            stats['evaporated'] = evap.sum().item()
        
        # Crystallize
        cryst = (state.alpha > cfg.crystallize_threshold) & has_pencil
        if cryst.any():
            state.pen[cryst] = state.pencil[cryst]
            state.pencil[cryst] = 0
            state.alpha[cryst] = 0
            stats['crystallized'] = cryst.sum().item()
        
        # Write new
        empty = (state.pen == 0) & (state.pencil == 0)
        write = empty & (max_p > cfg.write_threshold) & (conflict < cfg.high_conflict)
        if write.any():
            state.pencil[write] = best[write]
            state.alpha[write] = 0.1
            stats['written'] = write.sum().item()
        
        return stats
    
    def solve(self, puzzles, solutions=None, training=True):
        state = State(puzzles, solutions)
        agg = {'written': 0, 'evaporated': 0, 'crystallized': 0}
        
        for _ in range(self.cfg.max_cycles):
            logits, conflict, entropy = self.sense(state)
            stats = self.act(state, logits, conflict, entropy, training)
            for k in agg:
                agg[k] += stats[k]
            if (state.pen > 0).all():
                break
        
        logits, _, _ = self.sense(state)
        return state, logits, agg
    
    def forward(self, puzzles, solutions=None):
        state, logits, stats = self.solve(puzzles, solutions, training=True)
        return logits, self.diff.energy(logits), state, stats


def evaluate(model, loader, dev):
    model.eval()
    correct = total = evap = cryst = 0
    with torch.no_grad():
        for p, s in loader:
            p, s = p.to(dev), s.to(dev)
            state, logits, stats = model.solve(p, None, training=False)
            board = state.board()
            preds = torch.clamp(board - 1, 0, 8)
            unfilled = (board == 0)
            if unfilled.any():
                preds[unfilled] = logits.argmax(-1)[unfilled]
            mask = (p == 0)
            correct += ((preds == s) & mask).sum().item()
            total += mask.sum().item()
            evap += stats['evaporated']
            cryst += stats['crystallized']
    return correct / max(total, 1), evap, cryst


def run():
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    dev = "cuda" if torch.cuda.is_available() else "cpu"
    cfg = Config()
    edges, types = build_graph()
    model = Homeostat(cfg, edges, types).to(dev)
    
    train_p, train_s = generate_puzzles_with_clues(1000, 35, seed=42)
    test_p, test_s = generate_puzzles_with_clues(200, 35, seed=1042)
    
    train_dl = DataLoader(
        TensorDataset(torch.tensor(train_p, dtype=torch.long), torch.tensor(train_s-1, dtype=torch.long)),
        batch_size=cfg.batch_size, shuffle=True, drop_last=True
    )
    test_dl = DataLoader(
        TensorDataset(torch.tensor(test_p, dtype=torch.long), torch.tensor(test_s-1, dtype=torch.long)),
        batch_size=cfg.batch_size
    )
    
    opt = torch.optim.AdamW([
        {'params': [p for n,p in model.named_parameters() if 'pol' not in n], 'lr': cfg.lr},
        {'params': [model.diff.pol], 'lr': 0.05}
    ])
    sched = torch.optim.lr_scheduler.CosineAnnealingLR(opt, cfg.epochs)
    
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    os.makedirs(f"{cfg.log_dir}/run_{ts}", exist_ok=True)
    writer = SummaryWriter(f"{cfg.log_dir}/run_{ts}")
    
    print("=" * 100)
    print("v6.2: CORRECTNESS-AWARE HOMEOSTAT")
    print("=" * 100)
    print("Key: Alpha grows when pencil is CORRECT, decays when WRONG")
    print("-" * 100)
    print(f"{'Ep':>4} | {'Test':>6} | {'Evap':>6} | {'Cryst':>6} | {'g':>15} | Status")
    print("-" * 100)
    
    best = 0
    for epoch in range(cfg.epochs):
        model.train()
        for p, s in train_dl:
            p, s = p.to(dev), s.to(dev)
            opt.zero_grad()
            logits, energy, state, stats = model(p, s)
            loss = F.cross_entropy(logits.view(-1,9), s.view(-1), reduction='none')
            mask = (p == 0).view(-1).float()
            loss = (loss * mask).sum() / mask.sum() + 0.5 * energy
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            opt.step()
        sched.step()
        
        if epoch % cfg.log_interval == 0:
            acc, evap, cryst = evaluate(model, test_dl, dev)
            g = model.diff.g().detach().cpu().numpy()
            status = ""
            if acc > best:
                best = acc
                status = "BEST"
            if acc > 0.85:
                status += " BEATING v5!"
            if acc > 0.95:
                status += " GROKKING!"
            print(f"{epoch:>4} | {acc*100:>5.1f}% | {evap:>6} | {cryst:>6} | [{g[0]:.2f},{g[1]:.2f},{g[2]:.2f}] | {status}")
            writer.add_scalar("test/acc", acc, epoch)
    
    print("=" * 100)
    print(f"FINAL: {best*100:.1f}% (v5 was 85%)")
    if best > 0.85:
        print("*** HOMEOSTAT BEATS v5! ***")
    print("=" * 100)
    writer.close()
    return model, best


if __name__ == "__main__":
    model, acc = run()
