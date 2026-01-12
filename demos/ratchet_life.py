#!/usr/bin/env python3
"""
SGC Dynamics: The Evolutionary Ratchet

This demo visualizes Emergence as a Ratcheted Evolutionary Process.
Intelligence isn't random exploration—it's exploration that *locks in*
stable geometric structures (Phase Transitions), preventing them from
dissolving back into chaos.

The Narrative:
1. Exploration (Chaos): System randomly rewires, searching for stability
2. Selection (Geometry): Stable motifs (low stress) are identified as useful
3. The Ratchet (Memory): Stable structures are FROZEN/LOCKED
4. Evolution: Complexity accumulates in discrete steps (Phase Transitions)

Run with: streamlit run ratchet_life.py
"""

import streamlit as st
import numpy as np
import networkx as nx
from dataclasses import dataclass, field
from typing import Set, Tuple, List, Dict
import plotly.graph_objects as go
from collections import deque
import time

# Page configuration
st.set_page_config(
    page_title="SGC Evolutionary Ratchet",
    page_icon="🧬",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS
st.markdown("""
<style>
    .stApp {
        background-color: #0a0a0f;
    }
    .header-ratchet {
        background: linear-gradient(90deg, #ff4444, #ffd700, #00d4ff);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        font-size: 2.5rem;
        font-weight: bold;
        text-align: center;
    }
    .ratchet-on {
        background: linear-gradient(135deg, #1a2e1a 0%, #163e16 100%);
        border: 2px solid #00ff88;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
    }
    .ratchet-off {
        background: linear-gradient(135deg, #2e1a1a 0%, #3e1616 100%);
        border: 2px solid #ff4444;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
    }
    .crystal-badge {
        background: linear-gradient(135deg, #1a1a3e 0%, #16163e 100%);
        border: 1px solid #ffd700;
        border-radius: 5px;
        padding: 10px;
        text-align: center;
        color: #ffd700;
    }
    .phase-transition {
        animation: pulse-gold 1s ease-in-out;
    }
    @keyframes pulse-gold {
        0%, 100% { box-shadow: 0 0 10px #ffd700; }
        50% { box-shadow: 0 0 40px #ffd700; }
    }
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════════════════════
# EVOLUTIONARY RATCHET ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class EvolutionState:
    """State of the evolving network."""
    graph: nx.Graph
    locked_edges: Set[Tuple[int, int]] = field(default_factory=set)
    locked_nodes: Set[int] = field(default_factory=set)
    generation: int = 0
    complexity_history: List[float] = field(default_factory=list)
    phase_transitions: List[int] = field(default_factory=list)
    last_lock_gen: int = 0


class EvolutionaryRatchet:
    """
    The Ratchet: A mechanism that allows complexity to accumulate
    by locking in stable structures and preventing backsliding.
    """
    
    def __init__(self, n_nodes: int = 30, seed: int = None):
        self.n_nodes = n_nodes
        self.rng = np.random.default_rng(seed)
        self.stress_threshold = 0.3  # Below this = stable = LOCK
        self.perturb_rate = 0.15
        
        # Initialize with sparse random graph
        self.state = self._create_initial_state()
    
    def _create_initial_state(self) -> EvolutionState:
        """Create initial random graph."""
        G = nx.gnm_random_graph(self.n_nodes, self.n_nodes // 2, seed=42)
        
        # Assign random positions
        pos = nx.spring_layout(G, seed=42, k=2.0)
        for node in G.nodes():
            G.nodes[node]['pos'] = pos[node]
        
        return EvolutionState(graph=G)
    
    def reset(self):
        """Reset to initial state."""
        self.state = self._create_initial_state()
    
    def compute_edge_stress(self, edge: Tuple[int, int]) -> float:
        """
        Compute geometric stress for an edge.
        Uses local clustering and centrality as proxy for curvature.
        """
        G = self.state.graph
        u, v = edge
        
        if not G.has_edge(u, v):
            return 1.0
        
        # Local clustering coefficient average
        try:
            c_u = nx.clustering(G, u)
            c_v = nx.clustering(G, v)
            clustering = (c_u + c_v) / 2
        except:
            clustering = 0
        
        # Degree variance (high variance = unstable)
        d_u = G.degree(u)
        d_v = G.degree(v)
        degree_balance = 1.0 - abs(d_u - d_v) / (max(d_u, d_v) + 1)
        
        # Triangle participation (more triangles = more stable)
        common = len(list(nx.common_neighbors(G, u, v)))
        triangle_bonus = min(common / 3, 1.0)
        
        # Stress = inverse of stability
        stability = 0.3 * clustering + 0.3 * degree_balance + 0.4 * triangle_bonus
        stress = 1.0 - stability
        
        return stress
    
    def compute_global_complexity(self) -> float:
        """Compute overall network complexity/order."""
        G = self.state.graph
        
        if G.number_of_edges() == 0:
            return 0.0
        
        # Factors contributing to "complexity" (ordered structure)
        n_locked = len(self.state.locked_edges)
        n_edges = G.number_of_edges()
        lock_ratio = n_locked / max(n_edges, 1)
        
        # Average clustering
        try:
            avg_clustering = nx.average_clustering(G)
        except:
            avg_clustering = 0
        
        # Connected component structure
        n_components = nx.number_connected_components(G)
        component_order = 1.0 / (1 + n_components * 0.1)
        
        # Triangle count (motif richness)
        triangles = sum(nx.triangles(G).values()) // 3
        triangle_density = min(triangles / max(self.n_nodes, 1), 1.0)
        
        complexity = (
            0.4 * lock_ratio +
            0.2 * avg_clustering +
            0.2 * component_order +
            0.2 * triangle_density
        )
        
        return complexity
    
    def perturb(self):
        """Randomly perturb unlocked parts of the graph."""
        G = self.state.graph
        
        # Only perturb unlocked edges
        unlocked_edges = [
            e for e in G.edges()
            if self._normalize_edge(e) not in self.state.locked_edges
        ]
        
        # Possibly remove some unlocked edges
        for edge in unlocked_edges:
            if self.rng.random() < self.perturb_rate:
                G.remove_edge(*edge)
        
        # Possibly add new edges between unlocked nodes
        unlocked_nodes = [
            n for n in G.nodes()
            if n not in self.state.locked_nodes
        ]
        
        if len(unlocked_nodes) >= 2:
            for _ in range(max(1, len(unlocked_nodes) // 5)):
                if self.rng.random() < self.perturb_rate:
                    u, v = self.rng.choice(unlocked_nodes, size=2, replace=False)
                    if not G.has_edge(u, v):
                        G.add_edge(u, v)
    
    def _normalize_edge(self, edge: Tuple[int, int]) -> Tuple[int, int]:
        """Normalize edge tuple for consistent hashing."""
        return (min(edge), max(edge))
    
    def ratchet_step(self) -> int:
        """
        The Ratchet: Lock in stable structures.
        Returns number of newly locked edges.
        """
        G = self.state.graph
        newly_locked = 0
        
        for edge in list(G.edges()):
            norm_edge = self._normalize_edge(edge)
            
            if norm_edge in self.state.locked_edges:
                continue  # Already locked
            
            stress = self.compute_edge_stress(edge)
            
            if stress < self.stress_threshold:
                # LOCK IT! This edge is stable.
                self.state.locked_edges.add(norm_edge)
                self.state.locked_nodes.add(edge[0])
                self.state.locked_nodes.add(edge[1])
                newly_locked += 1
        
        if newly_locked > 0:
            self.state.phase_transitions.append(self.state.generation)
            self.state.last_lock_gen = self.state.generation
        
        return newly_locked
    
    def evolve(self, ratchet_enabled: bool = True) -> int:
        """Run one evolution step. Returns number of newly locked edges."""
        self.state.generation += 1
        
        # Perturb (explore)
        self.perturb()
        
        # Ratchet (lock stable structures)
        newly_locked = 0
        if ratchet_enabled:
            newly_locked = self.ratchet_step()
        
        # Track complexity
        complexity = self.compute_global_complexity()
        self.state.complexity_history.append(complexity)
        
        # Update positions for visualization
        self._update_positions()
        
        return newly_locked
    
    def _update_positions(self):
        """Update node positions with physics simulation."""
        G = self.state.graph
        
        # Get current positions
        pos = {}
        for node in G.nodes():
            if 'pos' in G.nodes[node]:
                pos[node] = G.nodes[node]['pos']
            else:
                pos[node] = np.array([self.rng.random(), self.rng.random()])
        
        # Spring layout iteration (locked nodes move less)
        try:
            new_pos = nx.spring_layout(
                G, 
                pos=pos, 
                iterations=3, 
                k=2.0,
                seed=self.state.generation
            )
            
            for node in G.nodes():
                if node in self.state.locked_nodes:
                    # Locked nodes move very slowly (damped)
                    old = np.array(pos.get(node, [0, 0]))
                    new = np.array(new_pos[node])
                    G.nodes[node]['pos'] = old + 0.1 * (new - old)
                else:
                    # Unlocked nodes move freely
                    G.nodes[node]['pos'] = new_pos[node]
        except:
            pass
    
    def get_edge_colors(self) -> Dict[Tuple[int, int], str]:
        """Get color for each edge based on stress/locked status."""
        colors = {}
        G = self.state.graph
        
        for edge in G.edges():
            norm_edge = self._normalize_edge(edge)
            
            if norm_edge in self.state.locked_edges:
                # LOCKED = Gold/Cyan (crystallized)
                colors[edge] = '#ffd700'  # Gold
            else:
                # Unlocked = color by stress (red = hot/volatile)
                stress = self.compute_edge_stress(edge)
                if stress > 0.7:
                    colors[edge] = '#ff4444'  # Hot red
                elif stress > 0.4:
                    colors[edge] = '#ff8844'  # Orange
                else:
                    colors[edge] = '#44ff88'  # Cool green (about to lock)
        
        return colors


# ═══════════════════════════════════════════════════════════════════════════════
# VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

def create_network_figure(ratchet: EvolutionaryRatchet) -> go.Figure:
    """Create Plotly figure of the network."""
    G = ratchet.state.graph
    edge_colors = ratchet.get_edge_colors()
    
    # Extract positions
    pos = {}
    for node in G.nodes():
        if 'pos' in G.nodes[node]:
            p = G.nodes[node]['pos']
            pos[node] = (p[0] if isinstance(p, np.ndarray) else p[0],
                        p[1] if isinstance(p, np.ndarray) else p[1])
        else:
            pos[node] = (0, 0)
    
    # Create edge traces (grouped by color for efficiency)
    edge_traces = []
    
    # Group edges by color
    color_groups = {}
    for edge in G.edges():
        color = edge_colors.get(edge, '#888888')
        if color not in color_groups:
            color_groups[color] = []
        color_groups[color].append(edge)
    
    # Create trace for each color group
    for color, edges in color_groups.items():
        x_edges = []
        y_edges = []
        
        for edge in edges:
            x0, y0 = pos[edge[0]]
            x1, y1 = pos[edge[1]]
            x_edges.extend([x0, x1, None])
            y_edges.extend([y0, y1, None])
        
        # Determine line width based on color (locked = thicker)
        width = 4 if color == '#ffd700' else 2
        
        edge_traces.append(go.Scatter(
            x=x_edges,
            y=y_edges,
            mode='lines',
            line=dict(color=color, width=width),
            hoverinfo='none',
            showlegend=False
        ))
    
    # Create node trace
    node_x = [pos[node][0] for node in G.nodes()]
    node_y = [pos[node][1] for node in G.nodes()]
    
    node_colors = [
        '#ffd700' if node in ratchet.state.locked_nodes else '#00d4ff'
        for node in G.nodes()
    ]
    
    node_sizes = [
        15 if node in ratchet.state.locked_nodes else 10
        for node in G.nodes()
    ]
    
    node_trace = go.Scatter(
        x=node_x,
        y=node_y,
        mode='markers',
        marker=dict(
            size=node_sizes,
            color=node_colors,
            line=dict(width=2, color='#0a0a0f')
        ),
        hoverinfo='text',
        text=[f"Node {n}<br>{'🔒 LOCKED' if n in ratchet.state.locked_nodes else '🔓 Unlocked'}"
              for n in G.nodes()],
        showlegend=False
    )
    
    # Create figure
    fig = go.Figure(data=edge_traces + [node_trace])
    
    fig.update_layout(
        template='plotly_dark',
        height=500,
        margin=dict(l=20, r=20, t=40, b=20),
        xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
        plot_bgcolor='rgba(10,10,15,1)',
        paper_bgcolor='rgba(10,10,15,1)',
        title=dict(
            text=f"Generation {ratchet.state.generation}",
            font=dict(size=16, color='#00d4ff'),
            x=0.5
        )
    )
    
    return fig


def create_complexity_chart(ratchet: EvolutionaryRatchet) -> go.Figure:
    """Create the complexity over time chart (staircase pattern)."""
    history = ratchet.state.complexity_history
    
    if len(history) < 2:
        history = [0] + list(history)
    
    fig = go.Figure()
    
    # Main complexity line
    fig.add_trace(go.Scatter(
        x=list(range(len(history))),
        y=history,
        mode='lines',
        name='Complexity',
        line=dict(color='#00d4ff', width=3),
        fill='tozeroy',
        fillcolor='rgba(0, 212, 255, 0.2)'
    ))
    
    # Mark phase transitions
    for pt in ratchet.state.phase_transitions:
        if pt < len(history):
            fig.add_vline(
                x=pt, 
                line_dash="dash", 
                line_color="#ffd700",
                line_width=1,
                opacity=0.7
            )
    
    fig.update_layout(
        template='plotly_dark',
        height=250,
        margin=dict(l=50, r=20, t=30, b=40),
        xaxis_title="Generation",
        yaxis_title="Complexity",
        yaxis=dict(range=[0, 1]),
        title=dict(
            text="The Staircase of Emergence",
            font=dict(size=14, color='#ffd700'),
            x=0.5
        )
    )
    
    return fig


# ═══════════════════════════════════════════════════════════════════════════════
# STREAMLIT UI
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    # Header
    st.markdown('<p class="header-ratchet">🧬 The Evolutionary Ratchet</p>', 
                unsafe_allow_html=True)
    st.markdown("""
    <div style="text-align: center; color: #888; margin-bottom: 20px;">
        <em>Watch complexity accumulate through locked-in phase transitions</em>
    </div>
    """, unsafe_allow_html=True)
    
    # Initialize ratchet in session state
    if 'ratchet' not in st.session_state:
        st.session_state.ratchet = EvolutionaryRatchet(n_nodes=30, seed=42)
    if 'auto_evolve' not in st.session_state:
        st.session_state.auto_evolve = False
    if 'last_lock_count' not in st.session_state:
        st.session_state.last_lock_count = 0
    
    ratchet = st.session_state.ratchet
    
    # Sidebar
    with st.sidebar:
        st.header("🎛️ Evolution Controls")
        
        ratchet_enabled = st.toggle(
            "🔒 Ratchet Enabled",
            value=True,
            help="When ON, stable structures get locked in permanently"
        )
        
        if ratchet_enabled:
            st.markdown('<div class="ratchet-on"><b>✨ RATCHET ACTIVE</b><br>Stable structures will crystallize</div>', 
                       unsafe_allow_html=True)
        else:
            st.markdown('<div class="ratchet-off"><b>⚠️ RATCHET OFF</b><br>No progress will be locked</div>', 
                       unsafe_allow_html=True)
        
        st.markdown("---")
        
        col1, col2 = st.columns(2)
        with col1:
            if st.button("⏭️ Step", use_container_width=True):
                newly_locked = ratchet.evolve(ratchet_enabled)
                st.session_state.last_lock_count = newly_locked
        
        with col2:
            if st.button("🔄 Reset", use_container_width=True):
                ratchet.reset()
                st.session_state.last_lock_count = 0
        
        # Multi-step evolution
        steps = st.slider("Evolution Steps", 1, 50, 10)
        if st.button(f"⚡ Evolve {steps} Steps", use_container_width=True):
            total_locked = 0
            for _ in range(steps):
                total_locked += ratchet.evolve(ratchet_enabled)
            st.session_state.last_lock_count = total_locked
        
        st.markdown("---")
        st.header("📊 Statistics")
        
        n_locked = len(ratchet.state.locked_edges)
        n_total = ratchet.state.graph.number_of_edges()
        lock_pct = (n_locked / max(n_total, 1)) * 100
        
        st.metric("Generation", ratchet.state.generation)
        st.metric("Locked Edges", f"{n_locked} / {n_total}")
        st.metric("Crystallization", f"{lock_pct:.1f}%")
        st.metric("Phase Transitions", len(ratchet.state.phase_transitions))
        
        st.markdown("---")
        st.header("📖 Theory")
        st.markdown("""
        **The Ratchet Principle:**
        
        Evolution isn't just random search—it's 
        search that *remembers* what works.
        
        **Red edges:** Hot, volatile, searching  
        **Gold edges:** Crystallized, locked, stable
        
        **Key Insight:**
        Without the ratchet, patterns form 
        but dissolve. With it, complexity 
        accumulates in discrete **steps**.
        """)
    
    # Main content
    
    # Row 1: Network visualization
    st.markdown("### 🧫 The Petri Dish: Neural Embryo")
    
    # Show phase transition alert if recent lock
    if st.session_state.last_lock_count > 0:
        st.success(f"🔒 **PHASE TRANSITION!** {st.session_state.last_lock_count} edges crystallized into stable structure")
        st.session_state.last_lock_count = 0
    
    fig_network = create_network_figure(ratchet)
    st.plotly_chart(fig_network, use_container_width=True)
    
    # Legend
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.markdown("🔴 **Red** = High stress (volatile)")
    with col2:
        st.markdown("🟠 **Orange** = Medium stress")
    with col3:
        st.markdown("🟢 **Green** = Low stress (ready to lock)")
    with col4:
        st.markdown("🟡 **Gold** = LOCKED (crystallized)")
    
    st.markdown("---")
    
    # Row 2: Complexity chart
    st.markdown("### 📈 The Pulse of Evolution")
    fig_complexity = create_complexity_chart(ratchet)
    st.plotly_chart(fig_complexity, use_container_width=True)
    
    # Interpretation
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("""
        **Without Ratchet:**
        - Patterns form randomly
        - They dissolve just as easily
        - No net progress accumulates
        - Complexity stays flat
        """)
    
    with col2:
        st.markdown("""
        **With Ratchet:**
        - Stable patterns get LOCKED
        - They become foundation for next layer
        - Complexity accumulates in STEPS
        - The "Staircase" of emergence
        """)
    
    # Footer
    st.markdown("---")
    st.markdown("""
    <div style="text-align: center; color: #666; font-size: 0.8rem;">
        <p>SGC Theory: Stable Geometry → Locked Structure → Accumulated Complexity</p>
        <p>Formally verified in <a href="https://github.com/JasonShroyer/sgc-lean" style="color: #00d4ff;">Lean4</a> | 
        Modules: SGC.Evolution.Dynamics, SGC.Thermodynamics.Evolution</p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    main()
