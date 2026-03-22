#!/usr/bin/env python3
"""
SGC Phase 1: Grokking Experiment - Live Dashboard
==================================================

Browser-based monitoring for the Grokking experiment with real-time
visualization of SGC metrics aligned with the Lean formalization.

Run with: streamlit run sgc_grokking_dashboard.py

Author: SGC Project | License: Apache 2.0
"""

import streamlit as st
import numpy as np
import torch
import torch.nn as nn
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
import time
import threading
from collections import deque

# Page configuration
st.set_page_config(
    page_title="SGC Grokking Monitor",
    page_icon="brain",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS for SGC theme
st.markdown("""
<style>
    .stApp {
        background-color: #0e1117;
    }
    .metric-card {
        background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
        border: 1px solid #0f3460;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
        margin: 5px;
    }
    .metric-value {
        font-size: 2rem;
        font-weight: bold;
        color: #00d4ff;
    }
    .metric-label {
        font-size: 0.85rem;
        color: #888;
        text-transform: uppercase;
        letter-spacing: 1px;
    }
    .phase-memorizing {
        color: #ff4444;
        font-weight: bold;
    }
    .phase-grokking {
        color: #00ff88;
        font-weight: bold;
    }
    .header-text {
        background: linear-gradient(90deg, #ff4444, #00d4ff, #00ff88);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        font-size: 2.2rem;
        font-weight: bold;
        text-align: center;
    }
    .lean-badge {
        background: #1a1a2e;
        border: 1px solid #00d4ff;
        border-radius: 5px;
        padding: 3px 8px;
        font-family: monospace;
        font-size: 0.75rem;
        color: #00d4ff;
    }
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════════════════════
# SGC METRICS (Lean-Aligned) - Same as sgc_grokking_phase1.py
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class SGCMetrics:
    """Container for SGC Phase 1 metrics, matching Lean formalization."""
    conflict_ratio: float
    fisher_rigidity: float
    complexity_cost: int
    variational_objective: float
    num_stiff_directions: int
    num_stable_directions: int
    num_consolidated: int


def compute_conflict_ratio_squared(S_basis: torch.Tensor, g: torch.Tensor) -> float:
    """ConflictRatio(S, g) = ||P_S g||^2 / ||g||^2 (SQUARED norms per Lean)"""
    if S_basis.shape[0] == 0:
        return 0.0
    g_sq = (g ** 2).sum().item()
    if g_sq == 0:
        return 0.0
    proj = S_basis @ g
    proj_sq = (proj ** 2).sum().item()
    return proj_sq / g_sq


def compute_fisher_rigidity(S_basis: torch.Tensor, F: torch.Tensor) -> float:
    """FisherRigidity(S) = Tr(P_S F P_S) = Tr(S F S^T)"""
    if S_basis.shape[0] == 0:
        return 0.0
    SFS = S_basis @ F @ S_basis.T
    return torch.trace(SFS).item()


def compute_fisher_rayleigh_quotient(F: torch.Tensor, v: torch.Tensor) -> float:
    """FisherRayleighQuotient(F, v) = (v^T F v) / (v^T v)"""
    vv = (v ** 2).sum().item()
    if vv == 0:
        return 0.0
    vFv = (v @ F @ v).item()
    return vFv / vv


def compute_gradient_stability(v: torch.Tensor, g: torch.Tensor, eps: float) -> bool:
    """GradientStability(v, g, eps) = |v . g| / ||v|| < eps"""
    v_norm = torch.norm(v).item()
    if v_norm == 0:
        return True
    v_dot_g = abs(torch.dot(v, g).item())
    return (v_dot_g / v_norm) < eps


# ═══════════════════════════════════════════════════════════════════════════════
# MODEL AND DATA
# ═══════════════════════════════════════════════════════════════════════════════

class ModularAdditionDataset(torch.utils.data.Dataset):
    """Dataset for modular addition: (a, b) -> (a + b) mod p"""
    
    def __init__(self, p: int = 97, train: bool = True, train_fraction: float = 0.3):
        self.p = p
        all_pairs = [(a, b) for a in range(p) for b in range(p)]
        all_labels = [(a + b) % p for a, b in all_pairs]
        
        n_train = int(len(all_pairs) * train_fraction)
        indices = list(range(len(all_pairs)))
        np.random.seed(42)
        np.random.shuffle(indices)
        
        if train:
            self.indices = indices[:n_train]
        else:
            self.indices = indices[n_train:]
        
        self.pairs = [all_pairs[i] for i in self.indices]
        self.labels = [all_labels[i] for i in self.indices]
    
    def __len__(self):
        return len(self.pairs)
    
    def __getitem__(self, idx):
        a, b = self.pairs[idx]
        label = self.labels[idx]
        x = torch.zeros(2 * self.p)
        x[a] = 1.0
        x[self.p + b] = 1.0
        return x, label


class GrokMLP(nn.Module):
    """Simple MLP for modular addition."""
    
    def __init__(self, p: int = 97, hidden_dim: int = 128):
        super().__init__()
        self.p = p
        self.net = nn.Sequential(
            nn.Linear(2 * p, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, hidden_dim),
            nn.ReLU(),
            nn.Linear(hidden_dim, p),
        )
    
    def forward(self, x):
        return self.net(x)


# ═══════════════════════════════════════════════════════════════════════════════
# TRAINING STATE
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class TrainingHistory:
    """Container for training history."""
    epochs: List[int]
    train_loss: List[float]
    train_acc: List[float]
    test_acc: List[float]
    conflict_ratio: List[float]
    fisher_rigidity: List[float]
    num_consolidated: List[int]
    variational_obj: List[float]
    
    @classmethod
    def empty(cls):
        return cls([], [], [], [], [], [], [], [])
    
    def add(self, epoch, loss, train_acc, test_acc, metrics: Optional[SGCMetrics]):
        self.epochs.append(epoch)
        self.train_loss.append(loss)
        self.train_acc.append(train_acc)
        self.test_acc.append(test_acc)
        if metrics:
            self.conflict_ratio.append(metrics.conflict_ratio)
            self.fisher_rigidity.append(metrics.fisher_rigidity)
            self.num_consolidated.append(metrics.num_consolidated)
            self.variational_obj.append(metrics.variational_objective)


# ═══════════════════════════════════════════════════════════════════════════════
# VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

def create_accuracy_chart(history: TrainingHistory) -> go.Figure:
    """Create train/test accuracy chart - the classic Grokking signature."""
    fig = go.Figure()
    
    fig.add_trace(go.Scatter(
        x=history.epochs, y=[a * 100 for a in history.train_acc],
        mode='lines', name='Train Accuracy',
        line=dict(color='#00d4ff', width=2)
    ))
    
    fig.add_trace(go.Scatter(
        x=history.epochs, y=[a * 100 for a in history.test_acc],
        mode='lines', name='Test Accuracy',
        line=dict(color='#ff4444', width=2)
    ))
    
    fig.update_layout(
        title="Grokking: Train vs Test Accuracy",
        xaxis_title="Epoch",
        yaxis_title="Accuracy (%)",
        yaxis_range=[0, 105],
        template="plotly_dark",
        height=350,
        legend=dict(x=0.02, y=0.98),
        margin=dict(l=50, r=20, t=50, b=50)
    )
    
    return fig


def create_conflict_chart(history: TrainingHistory) -> go.Figure:
    """Create ConflictRatio chart - should DROP at grokking."""
    if not history.conflict_ratio:
        return go.Figure()
    
    fig = go.Figure()
    
    # Use epochs where SGC metrics were computed
    sgc_epochs = history.epochs[-len(history.conflict_ratio):]
    
    fig.add_trace(go.Scatter(
        x=sgc_epochs, y=history.conflict_ratio,
        mode='lines+markers', name='Conflict Ratio',
        line=dict(color='#ff8800', width=2),
        marker=dict(size=6)
    ))
    
    fig.update_layout(
        title="SGC: Conflict Ratio ||P_S g||^2 / ||g||^2",
        xaxis_title="Epoch",
        yaxis_title="Conflict (squared)",
        template="plotly_dark",
        height=300,
        margin=dict(l=50, r=20, t=50, b=50)
    )
    
    return fig


def create_rigidity_chart(history: TrainingHistory) -> go.Figure:
    """Create FisherRigidity chart - should RISE at grokking."""
    if not history.fisher_rigidity:
        return go.Figure()
    
    fig = go.Figure()
    
    sgc_epochs = history.epochs[-len(history.fisher_rigidity):]
    
    fig.add_trace(go.Scatter(
        x=sgc_epochs, y=history.fisher_rigidity,
        mode='lines+markers', name='Fisher Rigidity',
        line=dict(color='#00ff88', width=2),
        marker=dict(size=6)
    ))
    
    fig.update_layout(
        title="SGC: Fisher Rigidity Tr(P_S F P_S)",
        xaxis_title="Epoch",
        yaxis_title="Rigidity",
        template="plotly_dark",
        height=300,
        margin=dict(l=50, r=20, t=50, b=50)
    )
    
    return fig


def create_dimension_chart(history: TrainingHistory) -> go.Figure:
    """Create Consolidated Dimension chart - should CHANGE at phase transition."""
    if not history.num_consolidated:
        return go.Figure()
    
    fig = go.Figure()
    
    sgc_epochs = history.epochs[-len(history.num_consolidated):]
    
    fig.add_trace(go.Scatter(
        x=sgc_epochs, y=history.num_consolidated,
        mode='lines+markers', name='k (consolidated)',
        line=dict(color='#d400ff', width=2),
        marker=dict(size=6)
    ))
    
    fig.update_layout(
        title="SGC: Dimension of Consolidated Subspace",
        xaxis_title="Epoch",
        yaxis_title="k (directions)",
        template="plotly_dark",
        height=300,
        margin=dict(l=50, r=20, t=50, b=50)
    )
    
    return fig


def create_combined_sgc_chart(history: TrainingHistory) -> go.Figure:
    """Create combined SGC metrics chart with dual y-axes."""
    if not history.conflict_ratio:
        return go.Figure()
    
    fig = make_subplots(specs=[[{"secondary_y": True}]])
    
    sgc_epochs = history.epochs[-len(history.conflict_ratio):]
    
    # Conflict on primary y-axis
    fig.add_trace(go.Scatter(
        x=sgc_epochs, y=history.conflict_ratio,
        mode='lines+markers', name='Conflict',
        line=dict(color='#ff8800', width=2),
        marker=dict(size=5)
    ), secondary_y=False)
    
    # Rigidity on secondary y-axis (normalized)
    if history.fisher_rigidity:
        max_rig = max(history.fisher_rigidity) if max(history.fisher_rigidity) > 0 else 1
        normalized_rig = [r / max_rig for r in history.fisher_rigidity]
        fig.add_trace(go.Scatter(
            x=sgc_epochs, y=normalized_rig,
            mode='lines+markers', name='Rigidity (norm)',
            line=dict(color='#00ff88', width=2),
            marker=dict(size=5)
        ), secondary_y=True)
    
    fig.update_layout(
        title="Triple Crossing: Conflict vs Rigidity",
        template="plotly_dark",
        height=350,
        legend=dict(x=0.02, y=0.98),
        margin=dict(l=50, r=50, t=50, b=50)
    )
    
    fig.update_xaxes(title_text="Epoch")
    fig.update_yaxes(title_text="Conflict", secondary_y=False, color='#ff8800')
    fig.update_yaxes(title_text="Rigidity (normalized)", secondary_y=True, color='#00ff88')
    
    return fig


# ═══════════════════════════════════════════════════════════════════════════════
# FISHER ESTIMATION
# ═══════════════════════════════════════════════════════════════════════════════

def estimate_fisher_diagonal(model, dataloader, device, num_samples=100):
    """Estimate diagonal of Fisher matrix (memory efficient)."""
    model.eval()
    params = [p for p in model.parameters() if p.requires_grad]
    n_params = sum(p.numel() for p in params)
    
    fisher_diag = torch.zeros(n_params, device=device)
    n_used = 0
    
    for x, y in dataloader:
        if n_used >= num_samples:
            break
        x, y = x.to(device), y.to(device)
        
        for i in range(min(len(x), num_samples - n_used)):
            model.zero_grad()
            logits = model(x[i:i+1])
            log_prob = torch.log_softmax(logits, dim=-1)
            loss = -log_prob[0, y[i]]
            loss.backward()
            
            g = torch.cat([p.grad.flatten() for p in params])
            fisher_diag += g ** 2
            n_used += 1
    
    fisher_diag /= n_used
    return fisher_diag


def compute_sgc_metrics_fast(model, dataloader, device, tau_stiff=0.1, eps_stable=0.5, lambda_cost=0.01):
    """Compute SGC metrics using diagonal Fisher approximation (faster)."""
    # Get Fisher diagonal
    fisher_diag = estimate_fisher_diagonal(model, dataloader, device, num_samples=50)
    
    # Get current gradient
    model.zero_grad()
    criterion = nn.CrossEntropyLoss()
    for x, y in dataloader:
        x, y = x.to(device), y.to(device)
        logits = model(x)
        loss = criterion(logits, y)
        loss.backward()
        break
    
    params = [p for p in model.parameters() if p.requires_grad]
    g = torch.cat([p.grad.flatten() for p in params])
    
    # Identify stiff directions (eigenvalue > tau)
    stiff_mask = fisher_diag > tau_stiff
    num_stiff = stiff_mask.sum().item()
    
    # Identify stable directions (low gradient)
    g_abs = torch.abs(g)
    stable_mask = g_abs < eps_stable
    num_stable = stable_mask.sum().item()
    
    # Consolidated = stiff AND stable
    consolidated_mask = stiff_mask & stable_mask
    num_consolidated = consolidated_mask.sum().item()
    
    # Conflict ratio (using diagonal approx)
    g_sq = (g ** 2).sum().item()
    if g_sq > 0 and num_consolidated > 0:
        proj_sq = ((g * consolidated_mask.float()) ** 2).sum().item()
        conflict_ratio = proj_sq / g_sq
    else:
        conflict_ratio = 0.0
    
    # Rigidity (sum of Fisher eigenvalues in S)
    fisher_rigidity = (fisher_diag * consolidated_mask.float()).sum().item()
    
    # Variational objective
    variational_obj = fisher_rigidity - lambda_cost * num_consolidated
    
    return SGCMetrics(
        conflict_ratio=conflict_ratio,
        fisher_rigidity=fisher_rigidity,
        complexity_cost=num_consolidated,
        variational_objective=variational_obj,
        num_stiff_directions=num_stiff,
        num_stable_directions=num_stable,
        num_consolidated=num_consolidated,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN DASHBOARD
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    # Header
    st.markdown('<p class="header-text">SGC Phase 1: Grokking Experiment</p>', unsafe_allow_html=True)
    st.markdown('<p style="text-align:center;color:#888;">Lean-Aligned ConflictRatio with Squared Norms</p>', unsafe_allow_html=True)
    
    # Sidebar controls
    st.sidebar.header("Experiment Configuration")
    
    p = st.sidebar.slider("Prime p (mod p addition)", 17, 113, 97, step=2)
    hidden_dim = st.sidebar.slider("Hidden dimension", 64, 256, 128)
    epochs = st.sidebar.slider("Epochs", 500, 10000, 3000)
    lr = st.sidebar.select_slider("Learning rate", [1e-4, 3e-4, 1e-3, 3e-3], value=1e-3)
    weight_decay = st.sidebar.slider("Weight decay", 0.1, 2.0, 1.0)
    train_fraction = st.sidebar.slider("Train fraction", 0.1, 0.5, 0.3)
    
    st.sidebar.header("SGC Thresholds")
    tau_stiff = st.sidebar.slider("tau_stiff (stiffness)", 0.01, 1.0, 0.1)
    eps_stable = st.sidebar.slider("eps_stable (stability)", 0.1, 2.0, 0.5)
    lambda_cost = st.sidebar.slider("lambda_cost (complexity)", 0.001, 0.1, 0.01)
    sgc_interval = st.sidebar.slider("SGC compute interval", 10, 100, 50)
    
    device = 'cuda' if torch.cuda.is_available() else 'cpu'
    st.sidebar.info(f"Device: {device}")
    
    # Run button
    if st.sidebar.button("Start Experiment", type="primary"):
        run_experiment(p, hidden_dim, epochs, lr, weight_decay, train_fraction,
                       tau_stiff, eps_stable, lambda_cost, sgc_interval, device)
    
    # Show Lean alignment info
    with st.expander("Lean Formalization Alignment"):
        st.markdown("""
        **This experiment matches the Lean formalization in `RenormalizationDynamics.lean`:**
        
        | Python | Lean Definition |
        |--------|-----------------|
        | `conflict_ratio` | `ConflictRatio S g = ||P_S g||^2 / ||g||^2` |
        | `fisher_rigidity` | `FisherRigidity state = Tr(S F S^T)` |
        | `num_consolidated` | `dim(S)` via `ComplexityCost` |
        | `variational_obj` | `VariationalObjective = Rigidity - lambda * Cost` |
        
        **DefectGatedConsolidationCriterion:**
        A direction is consolidated iff:
        1. **Stiff:** `FisherRayleighQuotient F v > tau_stiff`
        2. **Stable:** `GradientStability v g eps_stable`
        
        This prevents "hallucination lock-in" (confident but wrong).
        """)


def run_experiment(p, hidden_dim, epochs, lr, weight_decay, train_fraction,
                   tau_stiff, eps_stable, lambda_cost, sgc_interval, device):
    """Run the grokking experiment with live visualization."""
    
    # Initialize
    torch.manual_seed(42)
    np.random.seed(42)
    
    train_dataset = ModularAdditionDataset(p, train=True, train_fraction=train_fraction)
    test_dataset = ModularAdditionDataset(p, train=False, train_fraction=train_fraction)
    
    train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=512, shuffle=True)
    test_loader = torch.utils.data.DataLoader(test_dataset, batch_size=512, shuffle=False)
    
    model = GrokMLP(p, hidden_dim).to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    criterion = nn.CrossEntropyLoss()
    
    n_params = sum(p.numel() for p in model.parameters())
    st.info(f"Model: {n_params:,} parameters | Train: {len(train_dataset)} | Test: {len(test_dataset)}")
    
    history = TrainingHistory.empty()
    
    # Placeholders for live updates
    col1, col2 = st.columns(2)
    with col1:
        acc_chart_placeholder = st.empty()
    with col2:
        sgc_chart_placeholder = st.empty()
    
    col3, col4 = st.columns(2)
    with col3:
        conflict_placeholder = st.empty()
    with col4:
        rigidity_placeholder = st.empty()
    
    metrics_placeholder = st.empty()
    progress_bar = st.progress(0)
    status_text = st.empty()
    
    grokked = False
    grok_epoch = None
    
    for epoch in range(1, epochs + 1):
        # Training
        model.train()
        total_loss = 0
        correct = 0
        total = 0
        
        for x, y in train_loader:
            x, y = x.to(device), y.to(device)
            optimizer.zero_grad()
            logits = model(x)
            loss = criterion(logits, y)
            loss.backward()
            optimizer.step()
            
            total_loss += loss.item() * len(x)
            correct += (logits.argmax(dim=-1) == y).sum().item()
            total += len(x)
        
        train_loss = total_loss / total
        train_acc = correct / total
        
        # Testing
        model.eval()
        correct = 0
        total = 0
        with torch.no_grad():
            for x, y in test_loader:
                x, y = x.to(device), y.to(device)
                logits = model(x)
                correct += (logits.argmax(dim=-1) == y).sum().item()
                total += len(x)
        test_acc = correct / total
        
        # Compute SGC metrics periodically
        sgc_metrics = None
        if epoch % sgc_interval == 0 or epoch == 1:
            sgc_metrics = compute_sgc_metrics_fast(
                model, train_loader, device, tau_stiff, eps_stable, lambda_cost
            )
        
        history.add(epoch, train_loss, train_acc, test_acc, sgc_metrics)
        
        # Detect grokking
        if not grokked and test_acc > 0.95:
            grokked = True
            grok_epoch = epoch
        
        # Update visualizations every 10 epochs
        if epoch % 10 == 0 or epoch == 1:
            progress_bar.progress(epoch / epochs)
            
            phase = "GROKKING!" if grokked else "Memorizing..."
            phase_class = "phase-grokking" if grokked else "phase-memorizing"
            status_text.markdown(
                f'Epoch {epoch}/{epochs} | Train: {train_acc*100:.1f}% | Test: {test_acc*100:.1f}% | '
                f'<span class="{phase_class}">{phase}</span>',
                unsafe_allow_html=True
            )
            
            acc_chart_placeholder.plotly_chart(create_accuracy_chart(history), use_container_width=True)
            
            if history.conflict_ratio:
                sgc_chart_placeholder.plotly_chart(create_combined_sgc_chart(history), use_container_width=True)
                conflict_placeholder.plotly_chart(create_conflict_chart(history), use_container_width=True)
                rigidity_placeholder.plotly_chart(create_rigidity_chart(history), use_container_width=True)
            
            # Show current metrics
            if sgc_metrics:
                metrics_placeholder.markdown(f"""
                <div style="display: flex; justify-content: space-around;">
                    <div class="metric-card">
                        <div class="metric-value">{sgc_metrics.conflict_ratio:.3f}</div>
                        <div class="metric-label">Conflict Ratio</div>
                    </div>
                    <div class="metric-card">
                        <div class="metric-value">{sgc_metrics.fisher_rigidity:.1f}</div>
                        <div class="metric-label">Fisher Rigidity</div>
                    </div>
                    <div class="metric-card">
                        <div class="metric-value">{sgc_metrics.num_consolidated}</div>
                        <div class="metric-label">Consolidated k</div>
                    </div>
                    <div class="metric-card">
                        <div class="metric-value">{sgc_metrics.variational_objective:.1f}</div>
                        <div class="metric-label">Variational Obj</div>
                    </div>
                </div>
                """, unsafe_allow_html=True)
        
        # Early stopping
        if test_acc > 0.99:
            st.success(f"GROKKING COMPLETE at epoch {epoch}!")
            break
    
    # Final analysis
    st.header("Triple Crossing Signature Analysis")
    
    if grokked and len(history.conflict_ratio) > 1:
        # Find the crossing point
        test_accs = history.test_acc[-len(history.conflict_ratio):]
        max_jump_idx = 0
        max_jump = 0
        for i in range(1, len(test_accs)):
            jump = test_accs[i] - test_accs[i-1]
            if jump > max_jump:
                max_jump = jump
                max_jump_idx = i
        
        st.success(f"Phase transition detected at epoch ~{history.epochs[-len(history.conflict_ratio) + max_jump_idx]}")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            if max_jump_idx > 0 and history.conflict_ratio[max_jump_idx] < history.conflict_ratio[max_jump_idx-1]:
                st.success("Conflict DROPPED")
            else:
                st.warning("Conflict did not drop as expected")
        
        with col2:
            if max_jump_idx > 0 and history.fisher_rigidity[max_jump_idx] > history.fisher_rigidity[max_jump_idx-1]:
                st.success("Rigidity ROSE")
            else:
                st.warning("Rigidity did not rise as expected")
        
        with col3:
            if max_jump_idx > 0 and history.num_consolidated[max_jump_idx] != history.num_consolidated[max_jump_idx-1]:
                st.success("Dimension CHANGED")
            else:
                st.info("Dimension stayed constant")
    else:
        st.warning("No grokking detected in this run. Try more epochs or adjust hyperparameters.")


if __name__ == "__main__":
    main()
