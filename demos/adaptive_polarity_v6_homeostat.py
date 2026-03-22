"""
Adaptive Polarity Sheaf Network v6: The Confidence Homeostat

THEORY (SGC.Renormalization + SGC.Bridge.Quantum):
- The entity minimizes a Metabolic Functional: J = Conflict + Uncertainty + MetabolicCost
- "Pencil & Eraser" gives internal degrees of freedom (Ashby's Law of Requisite Variety)
- Confidence α flows on a manifold, not discrete decisions

THE THREE LAYERS:
1. Pen (Immutable): Ground truth (Clues + Finalized Commitments)
2. Pencil (Mutable): Current hypothesis map
3. Confidence (α ∈ [0,1]): Opacity of pencil marks

THE PHYSICS OF INPUT (Superposition):
    Input = (1 - α) · SheafState + α · OneHot(Pencil)
    
    α ≈ 0: Network is free to explore (High Entropy)
    α ≈ 1: Network is constrained by hypothesis (Low Entropy)

THE CONTROL LAWS (Homeostat):
1. SENSE: Run diffusion, compute Local Repulsion Energy (E_repl)
2. EVALUATE:
   - E_repl LOW  → Hypothesis fits topology → α += η_growth (Anneal)
   - E_repl HIGH → Hypothesis violates topology → α -= δ_decay (Melt)
3. ACT (Phase Transition):
   - α > 0.95 → CRYSTALLIZE: Pencil → Pen (Irreversible)
   - α < 0.0  → EVAPORATE: Reset Pencil to 0 (Backtracking!)

VITAL SIGNS (Abort Criteria):
- Eraser Check: Does the agent ever erase? If 0, δ too low.
- Confidence Gradient: Does α correlate with 1-Entropy?
- Conflict Check: Does energy decrease monotonically?
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
class ConfidenceHomeostatConfig:
    """Configuration derived from SGC Theory."""
    
    stalk_dim: int = 64
    num_cells: int = 81
    num_digits: int = 9
    
    # Diffusion
    diffusion_steps: int = 5
    diffusion_dt: float = 0.1
    
    # === CONFIDENCE DYNAMICS (The Homeostat) ===
    # Growth rate when hypothesis fits (low conflict)
    eta_growth: float = 0.25  # Increased for faster crystallization
    # Decay rate when hypothesis violates (high conflict)
    delta_decay: float = 0.30  # Must be > eta_growth for instability to be possible
    
    # Phase transition thresholds
    crystallize_threshold: float = 0.85  # Lowered from 0.95 for faster commitment
    evaporate_threshold: float = 0.0     # α below this → Erase
    
    # Conflict thresholds (derived from information theory)
    # E_repl normalized: 0 = no conflict, 1 = max conflict
    low_conflict_threshold: float = 0.1   # Below this, α grows
    high_conflict_threshold: float = 0.3  # Above this, α decays
    
    # Initial write threshold (when to write new pencil mark)
    write_confidence_threshold: float = 0.6  # Probability must exceed this
    
    # Cognitive cycles
    max_cycles: int = 4  # Bounded computation
    
    # Polarity (learnable)
    polarity_init: float = -0.5  # Slight repulsion bias
    
    # Training
    epochs: int = 150
    batch_size: int = 32
    lr: float = 1e-3
    polarity_lr: float = 0.05
    weight_decay: float = 0.01
    
    # Monitoring
    log_interval: int = 10
    vital_check_interval: int = 10  # Check vitals every N batches
    log_dir: str = "logs/adaptive_polarity_v6"


def build_sudoku_graph() -> Tuple[List[Tuple[int, int]], Dict[str, List[int]]]:
    """Build Sudoku constraint graph."""
    edges = []
    edge_types = {'row': [], 'col': [], 'box': []}
    edge_idx = 0
    
    for r in range(9):
        for c1 in range(9):
            for c2 in range(c1 + 1, 9):
                edges.append((r * 9 + c1, r * 9 + c2))
                edge_types['row'].append(edge_idx)
                edge_idx += 1
    
    for c in range(9):
        for r1 in range(9):
            for r2 in range(r1 + 1, 9):
                edges.append((r1 * 9 + c, r2 * 9 + c))
                edge_types['col'].append(edge_idx)
                edge_idx += 1
    
    for box_r in range(3):
        for box_c in range(3):
            cells = [(box_r*3+dr)*9 + box_c*3+dc for dr in range(3) for dc in range(3)]
            for i in range(len(cells)):
                for j in range(i + 1, len(cells)):
                    edges.append((cells[i], cells[j]))
                    edge_types['box'].append(edge_idx)
                    edge_idx += 1
    
    return edges, edge_types


class SudokuState:
    """
    The Three-Layer State (Confidence Manifold).
    
    Pen: Immutable ground truth
    Pencil: Mutable hypothesis
    Alpha: Confidence (opacity) of each pencil mark
    """
    
    def __init__(self, puzzles: torch.Tensor):
        B, N = puzzles.shape
        device = puzzles.device
        
        # Pen: Original clues (immutable during solve)
        self.pen = puzzles.clone()
        
        # Pencil: Current hypothesis (0 = no mark, 1-9 = digit)
        self.pencil = torch.zeros(B, N, dtype=torch.long, device=device)
        
        # Alpha: Confidence in each pencil mark (0.0 to 1.0)
        self.alpha = torch.zeros(B, N, device=device)
    
    def get_superposition_input(self, sheaf_state: torch.Tensor) -> torch.Tensor:
        """
        The Physics of Input:
        Input = (1 - α) · SheafState + α · OneHot(Pencil)
        
        This creates a superposition where:
        - α ≈ 0: Free exploration (sheaf dominates)
        - α ≈ 1: Constrained by hypothesis (one-hot dominates)
        """
        B, N, D = sheaf_state.shape
        device = sheaf_state.device
        
        # One-hot encoding of pencil marks (0 maps to zeros)
        pencil_onehot = F.one_hot(self.pencil, num_classes=10)[:, :, 1:]  # (B, N, 9)
        
        # For cells with no pencil mark, pencil_onehot is all zeros
        # We need to project this to stalk dimension
        # Simple approach: use first 9 dims of stalk for digit encoding
        pencil_embedding = torch.zeros(B, N, D, device=device)
        pencil_embedding[:, :, :9] = pencil_onehot.float()
        
        # Superposition: weighted blend
        alpha_expanded = self.alpha.unsqueeze(-1)  # (B, N, 1)
        
        # Only blend where there's a pencil mark
        has_pencil = (self.pencil > 0).unsqueeze(-1).float()
        
        superposition = (1 - alpha_expanded * has_pencil) * sheaf_state + \
                       (alpha_expanded * has_pencil) * pencil_embedding
        
        return superposition
    
    def get_effective_board(self) -> torch.Tensor:
        """Get board with pen + confident pencil marks."""
        board = self.pen.clone()
        # Add pencil marks where pen is empty
        mask = (self.pen == 0) & (self.pencil > 0)
        board[mask] = self.pencil[mask]
        return board
    
    def get_fixed_mask(self) -> torch.Tensor:
        """Mask of cells that are fixed (pen) or highly confident pencil."""
        return (self.pen > 0) | ((self.pencil > 0) & (self.alpha > 0.5))


class VitalSigns:
    """
    Monitor the physics of the system.
    
    If vitals fail, the physics is broken - ABORT and refine forces.
    """
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        self.evaporation_count = 0
        self.crystallization_count = 0
        self.energy_history = []
        self.alpha_entropy_correlation = []
    
    def record_evaporation(self, count: int):
        self.evaporation_count += count
    
    def record_crystallization(self, count: int):
        self.crystallization_count += count
    
    def record_energy(self, energy: float):
        self.energy_history.append(energy)
    
    def record_alpha_entropy(self, alpha: torch.Tensor, entropy: torch.Tensor):
        """Record correlation between α and (1 - entropy)."""
        # Normalize entropy to [0, 1] (max entropy for 9 classes is log(9) ≈ 2.2)
        norm_entropy = entropy / 2.2
        certainty = 1 - norm_entropy
        
        # Flatten and compute correlation
        alpha_flat = alpha.flatten().detach().cpu()
        certainty_flat = certainty.flatten().detach().cpu()
        
        # Only consider cells with pencil marks
        mask = alpha_flat > 0
        if mask.sum() > 10:
            corr = torch.corrcoef(torch.stack([alpha_flat[mask], certainty_flat[mask]]))[0, 1]
            if not torch.isnan(corr):
                self.alpha_entropy_correlation.append(corr.item())
    
    def check_vitals(self) -> Dict[str, bool]:
        """
        Check if the physics is healthy.
        
        Returns dict of vital signs with pass/fail status.
        """
        vitals = {}
        
        # 1. Eraser Check: Does the agent ever erase?
        vitals['eraser_active'] = self.evaporation_count > 0
        
        # 2. Confidence Gradient: α should correlate with certainty
        if len(self.alpha_entropy_correlation) > 5:
            mean_corr = np.mean(self.alpha_entropy_correlation[-10:])
            vitals['confidence_correlated'] = mean_corr > 0.0  # Should be positive
            vitals['correlation_value'] = mean_corr
        else:
            vitals['confidence_correlated'] = None
            vitals['correlation_value'] = None
        
        # 3. Conflict Check: Energy should generally decrease
        if len(self.energy_history) > 5:
            recent = self.energy_history[-10:]
            # Check if energy is trending down or at least not exploding
            vitals['energy_stable'] = recent[-1] < recent[0] * 1.5
            vitals['energy_trend'] = recent[-1] - recent[0]
        else:
            vitals['energy_stable'] = None
            vitals['energy_trend'] = None
        
        return vitals
    
    def get_summary(self) -> str:
        vitals = self.check_vitals()
        lines = [
            f"  Evaporations: {self.evaporation_count}",
            f"  Crystallizations: {self.crystallization_count}",
            f"  Eraser Active: {vitals['eraser_active']}",
        ]
        if vitals['correlation_value'] is not None:
            lines.append(f"  Alpha-Certainty Corr: {vitals['correlation_value']:.3f}")
        if vitals['energy_trend'] is not None:
            lines.append(f"  Energy Trend: {vitals['energy_trend']:.4f}")
        return "\n".join(lines)


class SheafDiffusion(nn.Module):
    """Sheaf diffusion with local conflict computation."""
    
    def __init__(self, edges, edge_types, stalk_dim, polarity_init):
        super().__init__()
        self.stalk_dim = stalk_dim
        
        src = torch.tensor([e[0] for e in edges], dtype=torch.long)
        dst = torch.tensor([e[1] for e in edges], dtype=torch.long)
        self.register_buffer('src', src)
        self.register_buffer('dst', dst)
        
        type_idx = torch.zeros(len(edges), dtype=torch.long)
        for t, (_, indices) in enumerate(edge_types.items()):
            for idx in indices:
                type_idx[idx] = t
        self.register_buffer('type_idx', type_idx)
        
        self.W = nn.ParameterList([
            nn.Parameter(torch.eye(stalk_dim) + 0.1 * torch.randn(stalk_dim, stalk_dim))
            for _ in range(3)
        ])
        self.polarity = nn.Parameter(torch.ones(3) * polarity_init)
    
    def get_g(self):
        return torch.sigmoid(self.polarity)
    
    def compute_local_conflict(self, logits: torch.Tensor) -> torch.Tensor:
        """
        Compute E_repl per cell (normalized to [0, 1]).
        
        This is the "pain" signal that drives confidence dynamics.
        """
        probs = F.softmax(logits, dim=-1)
        B = probs.shape[0]
        
        # Overlap with neighbors
        src_probs = probs[:, self.src, :]
        dst_probs = probs[:, self.dst, :]
        overlap = (src_probs * dst_probs).sum(dim=-1)  # (B, num_edges)
        
        # Aggregate to cells
        conflict = torch.zeros(B, 81, device=logits.device)
        conflict.scatter_add_(1, self.src.unsqueeze(0).expand(B, -1), overlap)
        conflict.scatter_add_(1, self.dst.unsqueeze(0).expand(B, -1), overlap)
        
        # Normalize by max possible (20 neighbors, max overlap 1 each)
        conflict = conflict / 20.0
        
        return conflict
    
    def compute_total_energy(self, logits: torch.Tensor) -> torch.Tensor:
        probs = F.softmax(logits, dim=-1)
        overlap = (probs[:, self.src, :] * probs[:, self.dst, :]).sum(dim=-1)
        return overlap.mean()
    
    def diffuse(self, stalks, logits, dt, fixed_mask):
        B, N, D = stalks.shape
        probs = F.softmax(logits, dim=-1)
        
        g = self.get_g()[self.type_idx].view(1, -1, 1)
        
        src_s = stalks[:, self.src, :]
        dst_s = stalks[:, self.dst, :]
        
        # Reactive repulsion: push proportional to overlap
        overlap = (probs[:, self.src, :] * probs[:, self.dst, :]).sum(-1, keepdim=True)
        
        # Flow direction
        diff = src_s - dst_s
        
        # Attractive flow (align)
        attr_flow = diff
        # Repulsive flow (separate when overlapping)
        repl_flow = -overlap * diff
        
        # Mix based on polarity
        flow_to_dst = g * attr_flow + (1 - g) * repl_flow
        flow_to_src = -flow_to_dst
        
        # Aggregate
        drift = torch.zeros_like(stalks)
        drift.scatter_add_(1, self.dst.view(1,-1,1).expand(B,-1,D), dt * flow_to_dst)
        drift.scatter_add_(1, self.src.view(1,-1,1).expand(B,-1,D), dt * flow_to_src)
        
        new_stalks = stalks + drift
        
        # Fixed cells don't move
        new_stalks = torch.where(fixed_mask.unsqueeze(-1), stalks, new_stalks)
        
        return new_stalks


class ConfidenceHomeostat(nn.Module):
    """
    The SGC Homeostat with Confidence Manifold.
    
    Implements the Sense → Evaluate → Act control loop.
    """
    
    def __init__(self, config: ConfidenceHomeostatConfig, edges, edge_types):
        super().__init__()
        self.config = config
        
        self.embed = nn.Embedding(10, config.stalk_dim)
        self.mlp = nn.Sequential(
            nn.Linear(config.stalk_dim, config.stalk_dim * 2),
            nn.ReLU(),
            nn.Linear(config.stalk_dim * 2, config.stalk_dim),
        )
        self.diffusion = SheafDiffusion(edges, edge_types, config.stalk_dim, config.polarity_init)
        self.head = nn.Linear(config.stalk_dim, 9)
        
        self.vitals = VitalSigns()
    
    def compute_entropy(self, logits: torch.Tensor) -> torch.Tensor:
        probs = F.softmax(logits, dim=-1)
        log_probs = F.log_softmax(logits, dim=-1)
        entropy = -(probs * log_probs).sum(dim=-1)
        return entropy
    
    def sense(self, state: SudokuState) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        """
        SENSE Phase: Run diffusion, compute beliefs and conflict.
        
        Returns: logits, conflict, entropy
        """
        config = self.config
        
        # Start with embedded board
        board = state.get_effective_board()
        stalks = self.embed(board)
        stalks = stalks + self.mlp(stalks)
        
        # Apply superposition with pencil hypothesis
        stalks = state.get_superposition_input(stalks)
        
        # Diffusion with fixed mask
        fixed_mask = state.get_fixed_mask()
        
        for _ in range(config.diffusion_steps):
            logits = self.head(stalks)
            stalks = self.diffusion.diffuse(stalks, logits, config.diffusion_dt, fixed_mask)
            stalks = stalks + 0.1 * self.mlp(stalks)
        
        logits = self.head(stalks)
        conflict = self.diffusion.compute_local_conflict(logits)
        entropy = self.compute_entropy(logits)
        
        return logits, conflict, entropy
    
    def evaluate_and_act(self, state: SudokuState, logits: torch.Tensor, 
                         conflict: torch.Tensor, entropy: torch.Tensor) -> Dict:
        """
        EVALUATE + ACT Phase: Update confidence based on conflict, execute phase transitions.
        
        Returns: statistics dict
        """
        config = self.config
        B = logits.shape[0]
        device = logits.device
        
        stats = {'written': 0, 'evaporated': 0, 'crystallized': 0}
        
        probs = F.softmax(logits, dim=-1)
        max_prob, best_digit = probs.max(dim=-1)  # (B, 81)
        best_digit = best_digit + 1  # Convert to 1-9
        
        # === EVALUATE: Update α based on conflict AND certainty ===
        has_pencil = (state.pencil > 0)
        
        # Certainty = 1 - normalized_entropy (high certainty = network is sure)
        certainty = 1.0 - (entropy / 2.2)  # Normalize by max entropy log(9)
        
        # Low conflict AND reasonable certainty → strengthen (anneal)
        good_fit = (conflict < config.low_conflict_threshold) & (certainty > 0.4) & has_pencil
        state.alpha[good_fit] += config.eta_growth
        
        # Moderate conditions → slow growth (not as good but not bad)
        ok_fit = ~good_fit & (conflict < config.high_conflict_threshold) & (certainty > 0.3) & has_pencil
        state.alpha[ok_fit] += config.eta_growth * 0.3
        
        # High conflict OR very low certainty → weaken (melt)
        bad_fit = ((conflict > config.high_conflict_threshold) | (certainty < 0.25)) & has_pencil
        state.alpha[bad_fit] -= config.delta_decay
        
        # Clamp α to valid range (allow negative for evaporation detection)
        # Don't clamp below 0 yet - we need to detect evaporation
        state.alpha = torch.clamp(state.alpha, -0.5, 1.0)
        
        # === ACT: Phase Transitions ===
        
        # 1. EVAPORATION: α < 0 → Erase pencil mark (BACKTRACKING!)
        evaporate_mask = (state.alpha < config.evaporate_threshold) & has_pencil
        evaporate_count = evaporate_mask.sum().item()
        if evaporate_count > 0:
            state.pencil[evaporate_mask] = 0
            state.alpha[evaporate_mask] = 0.0
            stats['evaporated'] = evaporate_count
            self.vitals.record_evaporation(evaporate_count)
        
        # 2. CRYSTALLIZATION: α > 0.95 → Move pencil to pen (IRREVERSIBLE)
        crystallize_mask = (state.alpha > config.crystallize_threshold) & has_pencil
        crystallize_count = crystallize_mask.sum().item()
        if crystallize_count > 0:
            state.pen[crystallize_mask] = state.pencil[crystallize_mask]
            state.pencil[crystallize_mask] = 0
            state.alpha[crystallize_mask] = 0.0
            stats['crystallized'] = crystallize_count
            self.vitals.record_crystallization(crystallize_count)
        
        # 3. WRITE NEW: High confidence prediction on empty cell
        empty = (state.pen == 0) & (state.pencil == 0)
        confident = (max_prob > config.write_confidence_threshold)
        # Also check for low conflict before writing
        low_conflict_for_write = (conflict < config.high_conflict_threshold)
        
        write_mask = empty & confident & low_conflict_for_write
        write_count = write_mask.sum().item()
        if write_count > 0:
            state.pencil[write_mask] = best_digit[write_mask]
            state.alpha[write_mask] = 0.1  # Start faint
            stats['written'] = write_count
        
        # Record vitals
        self.vitals.record_alpha_entropy(state.alpha, entropy)
        
        return stats
    
    def solve_cycle(self, state: SudokuState) -> Tuple[torch.Tensor, Dict]:
        """Run one complete Sense → Evaluate → Act cycle."""
        logits, conflict, entropy = self.sense(state)
        stats = self.evaluate_and_act(state, logits, conflict, entropy)
        
        energy = self.diffusion.compute_total_energy(logits)
        self.vitals.record_energy(energy.item())
        stats['energy'] = energy.item()
        stats['mean_conflict'] = conflict.mean().item()
        
        return logits, stats
    
    def solve(self, puzzles: torch.Tensor) -> Tuple[SudokuState, torch.Tensor, Dict]:
        """
        Solve puzzles using the cognitive loop.
        
        Returns: final state, final logits, aggregate stats
        """
        state = SudokuState(puzzles)
        
        agg_stats = {
            'total_written': 0,
            'total_evaporated': 0,
            'total_crystallized': 0,
            'cycles': 0,
        }
        
        for cycle in range(self.config.max_cycles):
            logits, stats = self.solve_cycle(state)
            
            agg_stats['total_written'] += stats['written']
            agg_stats['total_evaporated'] += stats['evaporated']
            agg_stats['total_crystallized'] += stats['crystallized']
            agg_stats['cycles'] += 1
            
            # Check if all cells filled
            if (state.pen > 0).all():
                break
        
        return state, logits, agg_stats
    
    def forward(self, puzzles: torch.Tensor, solutions: Optional[torch.Tensor] = None):
        """Forward pass for training."""
        state, logits, stats = self.solve(puzzles)
        energy = self.diffusion.compute_total_energy(logits)
        return logits, energy, state, stats


def evaluate(model, loader, device):
    model.eval()
    correct = total = 0
    total_evaporated = 0
    total_crystallized = 0
    
    with torch.no_grad():
        for puzzles, solutions in loader:
            puzzles, solutions = puzzles.to(device), solutions.to(device)
            
            state, logits, stats = model.solve(puzzles)
            
            # Get predictions
            board = state.get_effective_board()
            preds = board - 1  # Convert to 0-8
            preds = torch.clamp(preds, 0, 8)
            
            # For unfilled cells, use logits
            unfilled = (board == 0)
            if unfilled.any():
                logit_preds = logits.argmax(dim=-1)
                preds[unfilled] = logit_preds[unfilled]
            
            mask = (puzzles == 0)
            correct += ((preds == solutions) & mask).sum().item()
            total += mask.sum().item()
            
            total_evaporated += stats['total_evaporated']
            total_crystallized += stats['total_crystallized']
    
    return {
        'accuracy': correct / max(total, 1),
        'evaporated': total_evaporated,
        'crystallized': total_crystallized,
    }


def run_physics_test(full_scale=False):
    """
    Physics Test: Prove that the agent can write, feel pain, and erase.
    
    Goal: Demonstrate the write-pain-erase cycle works.
    """
    from baby_agi_sudoku import generate_puzzles_with_clues
    
    device = "cuda" if torch.cuda.is_available() else "cpu"
    
    if full_scale:
        config = ConfidenceHomeostatConfig(
            epochs=200,
            batch_size=32,
            max_cycles=6,  # More cycles for complex puzzles
        )
        n_train, n_test = 1000, 200
    else:
        config = ConfidenceHomeostatConfig(
            epochs=50,  # Short test
            batch_size=32,
        )
        n_train, n_test = 200, 100
    edges, edge_types = build_sudoku_graph()
    
    model = ConfidenceHomeostat(config, edges, edge_types).to(device)
    
    # Generate dataset
    train_p, train_s = generate_puzzles_with_clues(n_train, 35, seed=42)
    test_p, test_s = generate_puzzles_with_clues(n_test, 35, seed=1042)
    
    train_loader = DataLoader(
        TensorDataset(torch.tensor(train_p, dtype=torch.long), torch.tensor(train_s - 1, dtype=torch.long)),
        batch_size=config.batch_size, shuffle=True, drop_last=True
    )
    test_loader = DataLoader(
        TensorDataset(torch.tensor(test_p, dtype=torch.long), torch.tensor(test_s - 1, dtype=torch.long)),
        batch_size=config.batch_size
    )
    
    optimizer = torch.optim.AdamW([
        {'params': [p for n, p in model.named_parameters() if 'polarity' not in n], 
         'lr': config.lr, 'weight_decay': config.weight_decay},
        {'params': [model.diffusion.polarity], 'lr': config.polarity_lr, 'weight_decay': 0.0},
    ])
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_path = f"{config.log_dir}/physics_test_{timestamp}"
    os.makedirs(log_path, exist_ok=True)
    writer = SummaryWriter(log_path)
    
    print("=" * 100)
    print("v6 PHYSICS TEST: Confidence Homeostat")
    print("=" * 100)
    print(f"Goal: Prove write-pain-erase cycle")
    print(f"eta_growth={config.eta_growth}, delta_decay={config.delta_decay}")
    print("-" * 100)
    print(f"{'Ep':>4} | {'Test':>6} | {'Evap':>6} | {'Cryst':>6} | {'g':>15} | Vitals")
    print("-" * 100)
    
    for epoch in range(config.epochs):
        model.train()
        model.vitals.reset()  # Reset per epoch
        
        for batch_idx, (puzzles, solutions) in enumerate(train_loader):
            puzzles, solutions = puzzles.to(device), solutions.to(device)
            
            optimizer.zero_grad()
            logits, energy, state, stats = model(puzzles, solutions)
            
            # Loss
            loss_ce = F.cross_entropy(logits.view(-1, 9), solutions.view(-1), reduction='none')
            mask = (puzzles == 0).view(-1).float()
            loss_ce = (loss_ce * mask).sum() / mask.sum()
            
            loss = loss_ce + 0.5 * energy
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            optimizer.step()
        
        # Evaluate
        if epoch % config.log_interval == 0:
            results = evaluate(model, test_loader, device)
            g = model.diffusion.get_g().detach().cpu().numpy()
            vitals = model.vitals.check_vitals()
            
            vital_str = "OK" if vitals['eraser_active'] else "NO ERASE!"
            
            print(f"{epoch:>4} | {results['accuracy']*100:>5.1f}% | "
                  f"{results['evaporated']:>6} | {results['crystallized']:>6} | "
                  f"[{g[0]:.2f},{g[1]:.2f},{g[2]:.2f}] | {vital_str}")
            
            writer.add_scalar("test/acc", results['accuracy'], epoch)
            writer.add_scalar("homeostat/evaporated", results['evaporated'], epoch)
            writer.add_scalar("homeostat/crystallized", results['crystallized'], epoch)
    
    # Final vitals report
    print("=" * 100)
    print("VITAL SIGNS REPORT:")
    print(model.vitals.get_summary())
    
    vitals = model.vitals.check_vitals()
    if vitals['eraser_active']:
        print("\n[PASS] PHYSICS TEST PASSED: Agent can erase!")
        print("  The Homeostat has Requisite Variety.")
    else:
        print("\n[FAIL] PHYSICS TEST FAILED: No erasure detected!")
        print("  δ_decay too low or high_conflict_threshold too high.")
        print("  Recommendation: Increase δ_decay or lower high_conflict_threshold.")
    
    print("=" * 100)
    
    writer.close()
    return model, vitals


if __name__ == "__main__":
    import sys
    full_scale = "--full" in sys.argv
    model, vitals = run_physics_test(full_scale=full_scale)
