#!/usr/bin/env python3
"""
SGC Dynamics: Graph-Manifold Duality

The Ultimate SGC Demo - visualizing the mapping between:
- LEFT: Discrete Graph (The "Engine Room" - nodes and edges)
- RIGHT: Continuous Manifold (The "Projection" - spectral embedding)

Key Insight: "We fix the Graph to heal the Manifold"
As graph curvature decreases, the manifold embedding smooths from
a crumpled mess into a recognizable geometric shape.

Run with: streamlit run dual_view_evolution.py
"""

import streamlit as st
import numpy as np
import networkx as nx
from scipy import sparse
from scipy.sparse.linalg import eigsh
from dataclasses import dataclass, field
from typing import List, Tuple, Set, Optional
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# Page configuration
st.set_page_config(
    page_title="SGC Graph-Manifold Duality",
    page_icon="🌐",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS
st.markdown("""
<style>
    .stApp {
        background-color: #0a0a0f;
    }
    .header-dual {
        background: linear-gradient(90deg, #ff4444, #00d4ff);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        font-size: 2.2rem;
        font-weight: bold;
        text-align: center;
    }
    .graph-label {
        background: linear-gradient(135deg, #2e1a1a 0%, #3e1616 100%);
        border: 1px solid #ff4444;
        border-radius: 8px;
        padding: 10px;
        text-align: center;
        color: #ff6666;
    }
    .manifold-label {
        background: linear-gradient(135deg, #1a1a2e 0%, #16163e 100%);
        border: 1px solid #00d4ff;
        border-radius: 8px;
        padding: 10px;
        text-align: center;
        color: #00d4ff;
    }
    .emergence-alert {
        background: linear-gradient(135deg, #1a2e1a 0%, #163e16 100%);
        border: 2px solid #00ff88;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
        animation: pulse-green 2s infinite;
    }
    @keyframes pulse-green {
        0%, 100% { box-shadow: 0 0 10px #00ff88; }
        50% { box-shadow: 0 0 30px #00ff88; }
    }
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════════════════════
# GRAPH-MANIFOLD ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DualState:
    """State of the graph-manifold system."""
    graph: nx.Graph
    positions_3d: np.ndarray  # 3D positions for graph visualization
    spectral_coords: np.ndarray  # Spectral embedding (manifold)
    curvatures: np.ndarray  # Per-node curvature
    generation: int = 0
    total_curvature_history: List[float] = field(default_factory=list)
    manifold_smoothness_history: List[float] = field(default_factory=list)


class GraphManifoldEngine:
    """
    Engine for evolving a graph while tracking its manifold embedding.
    Demonstrates: Graph smoothing → Manifold un-crumpling.
    """
    
    def __init__(self, n_nodes: int = 50, seed: int = 42):
        self.n_nodes = n_nodes
        self.rng = np.random.default_rng(seed)
        self.flow_strength = 0.1
        self.rewire_rate = 0.05
        
        self.state = self._create_initial_state()
    
    def _create_initial_state(self) -> DualState:
        """Create initial chaotic graph."""
        # Start with random graph (messy hairball)
        G = nx.gnm_random_graph(self.n_nodes, self.n_nodes * 2, seed=42)
        
        # Ensure connected
        if not nx.is_connected(G):
            components = list(nx.connected_components(G))
            for i in range(len(components) - 1):
                u = list(components[i])[0]
                v = list(components[i + 1])[0]
                G.add_edge(u, v)
        
        # Random 3D positions (chaotic cloud)
        positions_3d = self.rng.standard_normal((self.n_nodes, 3))
        
        # Compute initial spectral embedding
        spectral_coords = self._compute_spectral_embedding(G)
        
        # Compute curvatures
        curvatures = self._compute_node_curvatures(G)
        
        return DualState(
            graph=G,
            positions_3d=positions_3d,
            spectral_coords=spectral_coords,
            curvatures=curvatures
        )
    
    def reset(self):
        """Reset to chaotic initial state."""
        self.state = self._create_initial_state()
    
    def _compute_spectral_embedding(self, G: nx.Graph) -> np.ndarray:
        """
        Compute Laplacian Eigenmap (spectral embedding).
        Uses eigenvectors 1, 2, 3 (skip 0 which is constant).
        """
        n = G.number_of_nodes()
        
        if n < 4:
            return np.zeros((n, 3))
        
        try:
            # Compute normalized Laplacian
            L = nx.normalized_laplacian_matrix(G).astype(float)
            
            # Get smallest eigenvectors (skip first which is constant)
            k = min(4, n - 1)
            eigenvalues, eigenvectors = eigsh(L, k=k, which='SM', tol=1e-3)
            
            # Use eigenvectors 1, 2, 3 as 3D coordinates
            coords = np.zeros((n, 3))
            for i in range(min(3, k - 1)):
                coords[:, i] = eigenvectors[:, i + 1]
            
            # Scale for visualization
            coords = coords * 3
            
            return coords
            
        except Exception as e:
            # Fallback to random if spectral fails
            return self.rng.standard_normal((n, 3))
    
    def _compute_node_curvatures(self, G: nx.Graph) -> np.ndarray:
        """
        Compute discrete curvature at each node.
        Uses Ollivier-Ricci inspired metric based on local structure.
        """
        curvatures = np.zeros(G.number_of_nodes())
        
        for node in G.nodes():
            neighbors = list(G.neighbors(node))
            degree = len(neighbors)
            
            if degree < 2:
                curvatures[node] = 1.0  # High curvature for leaf nodes
                continue
            
            # Count triangles (clustering)
            triangles = 0
            for i, n1 in enumerate(neighbors):
                for n2 in neighbors[i + 1:]:
                    if G.has_edge(n1, n2):
                        triangles += 1
            
            max_triangles = degree * (degree - 1) / 2
            clustering = triangles / max_triangles if max_triangles > 0 else 0
            
            # Curvature: high when few triangles (hyperbolic-like)
            # low when many triangles (flat/spherical-like)
            curvatures[node] = 1.0 - clustering
        
        return curvatures
    
    def _compute_manifold_smoothness(self) -> float:
        """
        Measure how "smooth" the manifold embedding is.
        Low variance in local neighborhoods = smooth.
        """
        coords = self.state.spectral_coords
        G = self.state.graph
        
        if coords.shape[0] < 2:
            return 0.0
        
        local_variances = []
        
        for node in G.nodes():
            neighbors = list(G.neighbors(node))
            if len(neighbors) == 0:
                continue
            
            # Get coordinates of node and neighbors
            node_coord = coords[node]
            neighbor_coords = coords[neighbors]
            
            # Compute variance of distances to neighbors
            distances = np.linalg.norm(neighbor_coords - node_coord, axis=1)
            variance = np.var(distances) if len(distances) > 1 else 0
            local_variances.append(variance)
        
        # Smoothness = inverse of average variance
        avg_variance = np.mean(local_variances) if local_variances else 1.0
        smoothness = 1.0 / (1.0 + avg_variance * 10)
        
        return smoothness
    
    def flow_step(self):
        """
        Perform one step of curvature flow (Yamabe-like).
        Smooths the graph by rewiring high-curvature regions.
        """
        G = self.state.graph
        curvatures = self.state.curvatures
        
        # Find high-curvature nodes
        high_curv_nodes = np.where(curvatures > 0.5)[0]
        
        for node in high_curv_nodes:
            if self.rng.random() > self.rewire_rate:
                continue
            
            neighbors = list(G.neighbors(node))
            if len(neighbors) < 2:
                continue
            
            # Try to add triangles (reduces curvature)
            for i, n1 in enumerate(neighbors):
                for n2 in neighbors[i + 1:]:
                    if not G.has_edge(n1, n2) and self.rng.random() < 0.3:
                        G.add_edge(n1, n2)
                        break
            
            # Remove redundant edges from very high degree nodes
            if len(neighbors) > 6 and self.rng.random() < 0.2:
                # Remove edge to lowest-triangle neighbor
                worst_neighbor = min(
                    neighbors,
                    key=lambda n: len(list(nx.common_neighbors(G, node, n)))
                )
                # Only remove if it doesn't disconnect
                if G.degree(worst_neighbor) > 1 and G.degree(node) > 1:
                    G.remove_edge(node, worst_neighbor)
    
    def evolve(self, flow_enabled: bool = True) -> None:
        """Evolve the system one step."""
        self.state.generation += 1
        
        if flow_enabled:
            self.flow_step()
        else:
            # Just random perturbation without healing
            self._random_perturb()
        
        # Update 3D positions (spring layout)
        self._update_graph_positions()
        
        # Recompute spectral embedding
        self.state.spectral_coords = self._compute_spectral_embedding(self.state.graph)
        
        # Recompute curvatures
        self.state.curvatures = self._compute_node_curvatures(self.state.graph)
        
        # Track metrics
        total_curv = np.mean(self.state.curvatures)
        smoothness = self._compute_manifold_smoothness()
        
        self.state.total_curvature_history.append(total_curv)
        self.state.manifold_smoothness_history.append(smoothness)
    
    def _random_perturb(self):
        """Random perturbation without intelligent flow."""
        G = self.state.graph
        edges = list(G.edges())
        
        # Random edge removal
        if edges and self.rng.random() < 0.1:
            edge = edges[self.rng.integers(len(edges))]
            if G.degree(edge[0]) > 1 and G.degree(edge[1]) > 1:
                G.remove_edge(*edge)
        
        # Random edge addition
        if self.rng.random() < 0.1:
            nodes = list(G.nodes())
            u, v = self.rng.choice(nodes, size=2, replace=False)
            if not G.has_edge(u, v):
                G.add_edge(u, v)
    
    def _update_graph_positions(self):
        """Update 3D positions using spring layout."""
        G = self.state.graph
        
        # Convert current positions to dict
        pos_dict = {i: self.state.positions_3d[i] for i in range(len(self.state.positions_3d))}
        
        try:
            # Spring layout in 3D
            new_pos = nx.spring_layout(
                G,
                pos=pos_dict,
                dim=3,
                iterations=5,
                k=1.5,
                seed=self.state.generation
            )
            
            # Update positions array
            for i in range(self.state.positions_3d.shape[0]):
                if i in new_pos:
                    self.state.positions_3d[i] = new_pos[i]
        except:
            pass
    
    def make_regular_lattice(self):
        """Transform to a regular lattice (target state)."""
        # Create grid graph
        side = int(np.sqrt(self.n_nodes))
        G = nx.grid_2d_graph(side, side)
        
        # Relabel nodes to integers
        mapping = {node: i for i, node in enumerate(G.nodes())}
        G = nx.relabel_nodes(G, mapping)
        
        # Add extra nodes if needed
        while G.number_of_nodes() < self.n_nodes:
            new_node = G.number_of_nodes()
            existing = list(G.nodes())[-1]
            G.add_edge(new_node, existing)
        
        self.state.graph = G
        
        # Update everything
        self.state.positions_3d = self.rng.standard_normal((G.number_of_nodes(), 3))
        self._update_graph_positions()
        self.state.spectral_coords = self._compute_spectral_embedding(G)
        self.state.curvatures = self._compute_node_curvatures(G)


# ═══════════════════════════════════════════════════════════════════════════════
# VISUALIZATION
# ═══════════════════════════════════════════════════════════════════════════════

def create_graph_figure(engine: GraphManifoldEngine, node_colors: np.ndarray) -> go.Figure:
    """Create 3D graph visualization (LEFT panel)."""
    G = engine.state.graph
    pos = engine.state.positions_3d
    curvatures = engine.state.curvatures
    n_nodes = len(pos)
    
    # Edge traces - color by curvature (red = high stress)
    edge_traces = []
    
    for edge in G.edges():
        x0, y0, z0 = pos[edge[0]]
        x1, y1, z1 = pos[edge[1]]
        
        # Edge color based on endpoint curvatures
        avg_curv = (curvatures[edge[0]] + curvatures[edge[1]]) / 2
        
        # Red for high curvature, blue for low
        if avg_curv > 0.6:
            edge_color = 'rgba(255, 80, 80, 0.8)'
            width = 3
        elif avg_curv > 0.3:
            edge_color = 'rgba(255, 180, 100, 0.6)'
            width = 2
        else:
            edge_color = 'rgba(100, 200, 255, 0.5)'
            width = 2
        
        edge_traces.append(go.Scatter3d(
            x=[x0, x1], y=[y0, y1], z=[z0, z1],
            mode='lines',
            line=dict(color=edge_color, width=width),
            hoverinfo='none',
            showlegend=False
        ))
    
    # Node trace - color by node ID (matches manifold)
    node_x = pos[:, 0]
    node_y = pos[:, 1]
    node_z = pos[:, 2]
    
    node_trace = go.Scatter3d(
        x=node_x, y=node_y, z=node_z,
        mode='markers',
        marker=dict(
            size=10,
            color=node_colors,
            colorscale='Viridis',
            cmin=0,
            cmax=n_nodes,
            colorbar=dict(
                title="Node ID",
                x=1.02,
                len=0.5
            ),
            line=dict(width=1, color='#0a0a0f')
        ),
        text=[f"Node {i}<br>Curvature: {curvatures[i]:.2f}" for i in range(n_nodes)],
        hoverinfo='text',
        showlegend=False
    )
    
    fig = go.Figure(data=edge_traces + [node_trace])
    
    fig.update_layout(
        template='plotly_dark',
        height=500,
        margin=dict(l=0, r=0, t=40, b=0),
        scene=dict(
            xaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title=''),
            yaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title=''),
            zaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title=''),
            bgcolor='rgba(10,10,15,1)',
            camera=dict(eye=dict(x=1.5, y=1.5, z=1.2))
        ),
        title=dict(
            text="GRAPH (Discrete Edges)",
            font=dict(size=14, color='#ff6666'),
            x=0.5
        )
    )
    
    return fig


def create_manifold_figure(engine: GraphManifoldEngine, node_colors: np.ndarray) -> go.Figure:
    """Create spectral embedding as a continuous SURFACE (RIGHT panel)."""
    coords = engine.state.spectral_coords
    n_nodes = len(coords)
    
    # Create Mesh3d surface using Delaunay triangulation (alphahull)
    # This wraps the points in a "skin" making it look like a continuous manifold
    mesh_trace = go.Mesh3d(
        x=coords[:, 0],
        y=coords[:, 1],
        z=coords[:, 2],
        alphahull=0,  # Convex hull (use -1 for Delaunay if points are good)
        opacity=0.5,
        color='#00d4ff',
        flatshading=True,
        lighting=dict(
            ambient=0.6,
            diffuse=0.8,
            specular=0.2,
            roughness=0.5
        ),
        lightposition=dict(x=100, y=100, z=200),
        hoverinfo='none',
        showlegend=False
    )
    
    # Also show points colored by node ID (matching graph)
    node_trace = go.Scatter3d(
        x=coords[:, 0],
        y=coords[:, 1],
        z=coords[:, 2],
        mode='markers',
        marker=dict(
            size=5,
            color=node_colors,
            colorscale='Viridis',
            cmin=0,
            cmax=n_nodes,
            showscale=False,
            line=dict(width=0)
        ),
        text=[f"Node {i}" for i in range(n_nodes)],
        hoverinfo='text',
        showlegend=False
    )
    
    fig = go.Figure(data=[mesh_trace, node_trace])
    
    fig.update_layout(
        template='plotly_dark',
        height=500,
        margin=dict(l=0, r=0, t=40, b=0),
        scene=dict(
            xaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title=''),
            yaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title=''),
            zaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title=''),
            bgcolor='rgba(10,10,15,1)',
            camera=dict(eye=dict(x=1.8, y=1.8, z=1.0))
        ),
        title=dict(
            text="MANIFOLD (Continuous Surface)",
            font=dict(size=14, color='#00d4ff'),
            x=0.5
        )
    )
    
    return fig


def create_metrics_chart(engine: GraphManifoldEngine) -> go.Figure:
    """Create dual metrics chart."""
    curv_history = engine.state.total_curvature_history
    smooth_history = engine.state.manifold_smoothness_history
    
    if len(curv_history) < 2:
        curv_history = [0.5] + list(curv_history)
        smooth_history = [0.3] + list(smooth_history)
    
    fig = go.Figure()
    
    # Curvature trace (should decrease)
    fig.add_trace(go.Scatter(
        x=list(range(len(curv_history))),
        y=curv_history,
        mode='lines',
        name='Graph Curvature',
        line=dict(color='#ff4444', width=3)
    ))
    
    # Smoothness trace (should increase)
    fig.add_trace(go.Scatter(
        x=list(range(len(smooth_history))),
        y=smooth_history,
        mode='lines',
        name='Manifold Smoothness',
        line=dict(color='#00d4ff', width=3)
    ))
    
    fig.update_layout(
        template='plotly_dark',
        height=200,
        margin=dict(l=50, r=20, t=30, b=40),
        xaxis_title="Generation",
        yaxis_title="Value",
        yaxis=dict(range=[0, 1]),
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="center", x=0.5),
        title=dict(
            text="The Duality: Curvature ↓ = Smoothness ↑",
            font=dict(size=12, color='#888'),
            x=0.5
        )
    )
    
    return fig


# ═══════════════════════════════════════════════════════════════════════════════
# STREAMLIT UI
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    # Header
    st.markdown('<p class="header-dual">🌐 Graph-Manifold Duality</p>', 
                unsafe_allow_html=True)
    st.markdown("""
    <div style="text-align: center; color: #888; margin-bottom: 20px;">
        <em>"We fix the Graph to heal the Manifold"</em>
    </div>
    """, unsafe_allow_html=True)
    
    # Initialize engine and auto-play state
    if 'gm_engine' not in st.session_state:
        st.session_state.gm_engine = GraphManifoldEngine(n_nodes=40, seed=42)
    if 'auto_play' not in st.session_state:
        st.session_state.auto_play = False
    
    engine = st.session_state.gm_engine
    
    # Sidebar
    with st.sidebar:
        st.header("🎛️ Flow Controls")
        
        flow_enabled = st.toggle(
            "🌊 Curvature Flow",
            value=True,
            help="Enable Yamabe-like flow to smooth the graph"
        )
        
        st.markdown("---")
        
        # Auto-play toggle
        auto_play = st.toggle(
            "▶️ Auto-Play",
            value=st.session_state.auto_play,
            help="Smooth animation loop"
        )
        st.session_state.auto_play = auto_play
        
        play_speed = st.slider("Speed", 1, 10, 5, help="Steps per frame")
        
        st.markdown("---")
        
        col1, col2 = st.columns(2)
        with col1:
            if st.button("⏭️ Step"):
                engine.evolve(flow_enabled)
        with col2:
            if st.button("🔄 Reset"):
                engine.reset()
                st.session_state.auto_play = False
        
        if st.button("🎯 Jump to Lattice",
                    help="Transform to regular grid (target state)"):
            engine.make_regular_lattice()
        
        st.markdown("---")
        st.header("📊 Current State")
        
        avg_curv = np.mean(engine.state.curvatures)
        smoothness = engine._compute_manifold_smoothness()
        
        st.metric("Generation", engine.state.generation)
        st.metric("Avg Curvature", f"{avg_curv:.3f}")
        st.metric("Manifold Smoothness", f"{smoothness:.3f}")
        st.metric("Edges", engine.state.graph.number_of_edges())
        
        # Status indicator
        if avg_curv < 0.3 and smoothness > 0.6:
            st.markdown('<div class="emergence-alert"><b>✨ EMERGENCE!</b><br>Manifold has unfolded</div>', 
                       unsafe_allow_html=True)
        
        st.markdown("---")
        st.header("📖 Theory")
        st.markdown("""
        **Node Colors:** Same on both sides!
        Track how graph nodes map to manifold.
        
        **Edge Colors (Left):**
        - 🔴 Red = High curvature (stressed)
        - 🔵 Blue = Low curvature (relaxed)
        
        **Surface (Right):**
        - Crumpled = High entropy
        - Smooth = Emerged structure
        """)
    
    # Create node colors (by node ID - consistent across both views)
    n_nodes = engine.state.graph.number_of_nodes()
    node_colors = np.arange(n_nodes)
    
    # Auto-play animation loop
    if st.session_state.auto_play:
        import time
        
        # Create placeholders for smooth updates
        graph_placeholder = st.empty()
        manifold_placeholder = st.empty()
        metrics_placeholder = st.empty()
        
        # Animation loop
        for _ in range(100):  # Max iterations
            if not st.session_state.auto_play:
                break
            
            # Evolve
            for _ in range(play_speed):
                engine.evolve(flow_enabled)
            
            # Update visualizations in place
            col_left, col_right = graph_placeholder.columns(2)
            
            with col_left:
                st.markdown('<div class="graph-label"><b>🔴 ENGINE ROOM</b><br>Discrete Graph</div>', 
                           unsafe_allow_html=True)
                fig_graph = create_graph_figure(engine, node_colors)
                st.plotly_chart(fig_graph, use_container_width=True, key=f"graph_{engine.state.generation}")
            
            with col_right:
                st.markdown('<div class="manifold-label"><b>🔵 PROJECTION</b><br>Spectral Surface</div>', 
                           unsafe_allow_html=True)
                fig_manifold = create_manifold_figure(engine, node_colors)
                st.plotly_chart(fig_manifold, use_container_width=True, key=f"manifold_{engine.state.generation}")
            
            # Update metrics
            with metrics_placeholder.container():
                st.markdown("### 📈 Curvature ↓ = Smoothness ↑")
                fig_metrics = create_metrics_chart(engine)
                st.plotly_chart(fig_metrics, use_container_width=True, key=f"metrics_{engine.state.generation}")
            
            time.sleep(0.1)
            
            # Check for emergence
            avg_curv = np.mean(engine.state.curvatures)
            if avg_curv < 0.25:
                st.session_state.auto_play = False
                st.balloons()
                break
        
        st.rerun()
    
    else:
        # Static display (no auto-play)
        col_left, col_right = st.columns(2)
        
        with col_left:
            st.markdown('<div class="graph-label"><b>🔴 ENGINE ROOM</b><br>Discrete Graph</div>', 
                       unsafe_allow_html=True)
            fig_graph = create_graph_figure(engine, node_colors)
            st.plotly_chart(fig_graph, use_container_width=True)
        
        with col_right:
            st.markdown('<div class="manifold-label"><b>🔵 PROJECTION</b><br>Spectral Surface</div>', 
                       unsafe_allow_html=True)
            fig_manifold = create_manifold_figure(engine, node_colors)
            st.plotly_chart(fig_manifold, use_container_width=True)
        
        # Metrics chart
        st.markdown("---")
        st.markdown("### 📈 Curvature ↓ = Smoothness ↑")
        fig_metrics = create_metrics_chart(engine)
        st.plotly_chart(fig_metrics, use_container_width=True)
    
    # Legend
    col1, col2 = st.columns(2)
    with col1:
        st.caption("🔴 **Graph:** Red edges = stressed, Blue = relaxed. Nodes colored by ID.")
    with col2:
        st.caption("🔵 **Manifold:** Semi-transparent surface wraps spectral embedding. Same node colors.")
    
    # Footer
    st.markdown("---")
    st.markdown("""
    <div style="text-align: center; color: #666; font-size: 0.8rem;">
        <p>SGC Theory: Discrete Graph ↔ Continuous Manifold | Curvature Flow = Geometric Healing</p>
        <p>Formally verified in <a href="https://github.com/JasonShroyer/sgc-lean" style="color: #00d4ff;">Lean4</a> | 
        Modules: SGC.Geometry.CurvatureBridge, SGC.Evolution.Dynamics</p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    main()
