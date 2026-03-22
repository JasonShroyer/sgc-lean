"""
Adaptive Polarity v6 Hybrid: Best of v5 + v6

KEY INSIGHT:
- v5 (Iterative Collapse) achieved 85% with direct supervision
- v6 (Homeostat) achieved 65.9% with write/erase/crystallize mechanics
- HYBRID: Use v5's collapse for HIGH confidence, v6's pencil for LOW confidence

THE ALGORITHM:
1. Run diffusion to get beliefs
2. For cells with VERY HIGH confidence (>0.9): Collapse directly (v5 style)
3. For cells with MODERATE confidence (0.5-0.9): Write pencil mark
4. Pencil marks evolve via homeostat dynamics (grow/decay based on conflict)
5. Crystallization promotes pencil -> pen when alpha reaches threshold

This gives us:
- Fast, accurate collapse for obvious cells (v5's strength)
- Reversible exploration for uncertain cells (v6's strength)
"""

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader, TensorDataset
from torch.utils.tensorboard import SummaryWriter
from dataclasses import dataclass
from typing import List, Tuple, Dict
from datetime import datetime
import os


@dataclass
class HybridConfig:
    stalk_dim: int = 64
    diffusion_steps: int = 6
    diffusion_dt: float = 0.1
    
    # v5-style collapse thresholds
    collapse_confidence: float = 0.9  # Very high -> direct collapse
    collapse_entropy: float = 0.5     # Low entropy -> ready to collapse
    
    # v6-style pencil thresholds
    pencil_confidence: float = 0.5    # Moderate -> write pencil
    
    # Homeostat dynamics
    eta_growth: float = 0.2
    delta_decay: float = 0.25
    crystallize_threshold: float = 0.85
    evaporate_threshold: float = 0.0
    
    low_conflict: float = 0.12
    high_conflict: float = 0.30
    
    max_iterations: int = 20  # More iterations for complex puzzles
    polarity_init: float = -0.5
    
    epochs: int = 200
    batch_size: int = 32
    lr: float = 1e-3
    log_interval: int = 10
    log_dir: str = "logs/adaptive_polarity_v6_hybrid"


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


class HybridState:
    """State with Pen (immutable) and Pencil (mutable with confidence)."""
    
    def __init__(self, puzzles):
        B = puzzles.shape[0]
        dev = puzzles.device
        self.pen = puzzles.clone()  # Clues + collapsed cells
        self.pencil = torch.zeros_like(puzzles)  # Tentative marks
        self.alpha = torch.zeros(B, 81, device=dev)  # Pencil confidence
    
    def board(self):
        """Effective board: pen takes priority, then pencil."""
        b = self.pen.clone()
        m = (self.pen == 0) & (self.pencil > 0)
        b[m] = self.pencil[m]
        return b
    
    def fixed(self):
        """Cells that are effectively fixed."""
        return (self.pen > 0) | ((self.pencil > 0) & (self.alpha > 0.5))
    
    def collapse(self, mask, digits):
        """v5-style direct collapse to pen."""
        self.pen[mask] = digits[mask]
    
    def write_pencil(self, mask, digits, initial_alpha=0.2):
        """v6-style write to pencil."""
        self.pencil[mask] = digits[mask]
        self.alpha[mask] = initial_alpha


class Diffusion(nn.Module):
    def __init__(self, edges, types, dim, pol_init):
        super().__init__()
        src = torch.tensor([e[0] for e in edges])
        dst = torch.tensor([e[1] for e in edges])
        self.register_buffer('src', src)
        self.register_buffer('dst', dst)
        
        tidx = torch.zeros(len(edges), dtype=torch.long)
        for t, (_, idxs) in enumerate(types.items()):
            for i in idxs:
                tidx[i] = t
        self.register_buffer('tidx', tidx)
        
        self.W = nn.ParameterList([nn.Parameter(torch.eye(dim)+0.1*torch.randn(dim,dim)) for _ in range(3)])
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
        return torch.where(fixed.unsqueeze(-1), s, s + drift)


class HybridHomeostat(nn.Module):
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
        """Run diffusion and compute beliefs."""
        cfg = self.cfg
        s = self.embed(state.board())
        s = s + self.mlp(s)
        fixed = state.fixed()
        
        for _ in range(cfg.diffusion_steps):
            logits = self.head(s)
            s = self.diff.step(s, logits, cfg.diffusion_dt, fixed)
            s = s + 0.1 * self.mlp(s)
        
        logits = self.head(s)
        return logits
    
    def compute_entropy(self, logits):
        p = F.softmax(logits, -1)
        return -(p * F.log_softmax(logits, -1)).sum(-1)
    
    def solve(self, puzzles):
        """Hybrid solve: v5 collapse + v6 pencil."""
        cfg = self.cfg
        state = HybridState(puzzles)
        stats = {'collapsed': 0, 'written': 0, 'evaporated': 0, 'crystallized': 0}
        
        for iteration in range(cfg.max_iterations):
            logits = self.sense(state)
            probs = F.softmax(logits, -1)
            max_prob, best = probs.max(-1)
            best_digit = best + 1  # 1-9
            
            entropy = self.compute_entropy(logits)
            conflict = self.diff.conflict(logits)
            
            # === PHASE 1: v5-style COLLAPSE for very confident cells ===
            empty = (state.pen == 0) & (state.pencil == 0)
            very_confident = (max_prob > cfg.collapse_confidence) & (entropy < cfg.collapse_entropy)
            collapse_mask = empty & very_confident
            
            if collapse_mask.any():
                state.collapse(collapse_mask, best_digit)
                stats['collapsed'] += collapse_mask.sum().item()
                continue  # Re-sense after collapse
            
            # === PHASE 2: Homeostat dynamics for pencil marks ===
            has_pencil = (state.pencil > 0)
            certainty = 1.0 - entropy / 2.2
            
            # Grow alpha for good pencil marks
            good = (conflict < cfg.low_conflict) & (certainty > 0.4) & has_pencil
            state.alpha[good] += cfg.eta_growth
            
            # Decay alpha for bad pencil marks
            bad = ((conflict > cfg.high_conflict) | (certainty < 0.3)) & has_pencil
            state.alpha[bad] -= cfg.delta_decay
            
            state.alpha = torch.clamp(state.alpha, -0.5, 1.0)
            
            # Evaporate (erase)
            evap = (state.alpha < cfg.evaporate_threshold) & has_pencil
            if evap.any():
                state.pencil[evap] = 0
                state.alpha[evap] = 0
                stats['evaporated'] += evap.sum().item()
            
            # Crystallize (pencil -> pen)
            cryst = (state.alpha > cfg.crystallize_threshold) & has_pencil
            if cryst.any():
                state.pen[cryst] = state.pencil[cryst]
                state.pencil[cryst] = 0
                state.alpha[cryst] = 0
                stats['crystallized'] += cryst.sum().item()
            
            # === PHASE 3: Write new pencil marks for moderate confidence ===
            empty = (state.pen == 0) & (state.pencil == 0)
            moderate = (max_prob > cfg.pencil_confidence) & (max_prob <= cfg.collapse_confidence)
            write_mask = empty & moderate & (conflict < cfg.high_conflict)
            
            if write_mask.any():
                state.write_pencil(write_mask, best_digit)
                stats['written'] += write_mask.sum().item()
            
            # Check if solved
            if (state.pen > 0).all():
                break
        
        final_logits = self.sense(state)
        return state, final_logits, stats
    
    def forward(self, puzzles):
        state, logits, stats = self.solve(puzzles)
        return logits, self.diff.energy(logits), state, stats


def evaluate(model, loader, dev):
    model.eval()
    correct = total = collapsed = evap = cryst = 0
    with torch.no_grad():
        for p, s in loader:
            p, s = p.to(dev), s.to(dev)
            state, logits, stats = model.solve(p)
            board = state.board()
            preds = torch.clamp(board - 1, 0, 8)
            unfilled = (board == 0)
            if unfilled.any():
                preds[unfilled] = logits.argmax(-1)[unfilled]
            mask = (p == 0)
            correct += ((preds == s) & mask).sum().item()
            total += mask.sum().item()
            collapsed += stats['collapsed']
            evap += stats['evaporated']
            cryst += stats['crystallized']
    return correct / max(total, 1), collapsed, evap, cryst


def run():
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    dev = "cuda" if torch.cuda.is_available() else "cpu"
    cfg = HybridConfig()
    edges, types = build_graph()
    model = HybridHomeostat(cfg, edges, types).to(dev)
    
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
    
    print("=" * 110)
    print("v6 HYBRID: v5 Collapse + v6 Pencil")
    print("=" * 110)
    print("High confidence (>0.9) -> Direct collapse")
    print("Moderate confidence (0.5-0.9) -> Pencil with homeostat")
    print("-" * 110)
    print(f"{'Ep':>4} | {'Test':>6} | {'Coll':>6} | {'Evap':>6} | {'Cryst':>6} | {'g':>15} | Status")
    print("-" * 110)
    
    best = 0
    for epoch in range(cfg.epochs):
        model.train()
        for p, s in train_dl:
            p, s = p.to(dev), s.to(dev)
            opt.zero_grad()
            logits, energy, state, stats = model(p)
            loss = F.cross_entropy(logits.view(-1,9), s.view(-1), reduction='none')
            mask = (p == 0).view(-1).float()
            loss = (loss * mask).sum() / mask.sum() + 0.5 * energy
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            opt.step()
        sched.step()
        
        if epoch % cfg.log_interval == 0:
            acc, coll, evap, cryst = evaluate(model, test_dl, dev)
            g = model.diff.g().detach().cpu().numpy()
            status = ""
            if acc > best:
                best = acc
                status = "BEST"
            if acc > 0.85:
                status += " BEATING v5!"
            if acc > 0.95:
                status += " GROKKING!"
            print(f"{epoch:>4} | {acc*100:>5.1f}% | {coll:>6} | {evap:>6} | {cryst:>6} | [{g[0]:.2f},{g[1]:.2f},{g[2]:.2f}] | {status}")
            writer.add_scalar("test/acc", acc, epoch)
            writer.add_scalar("collapsed", coll, epoch)
            writer.add_scalar("evaporated", evap, epoch)
            writer.add_scalar("crystallized", cryst, epoch)
    
    print("=" * 110)
    print(f"FINAL: {best*100:.1f}% (v5 was 85%)")
    if best > 0.85:
        print("*** HYBRID BEATS v5! ***")
    elif best > 0.80:
        print("Close to v5, homeostat adding value")
    print("=" * 110)
    writer.close()
    return model, best


if __name__ == "__main__":
    model, acc = run()
