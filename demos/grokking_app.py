#!/usr/bin/env python3
"""
SGC Dynamics: Visualizing the 'Grokking' Phase Transition

This demo visualizes how SGC (Spectral Geometry of Curvature) theory can
detect the difference between "memorization" and "true understanding" in
neural network training - the phenomenon known as "Grokking".

The key insight: Standard metrics (Loss) show learning early, but SGC metrics
reveal the hidden geometric phase transition where the model shifts from
memorizing specific examples to discovering the underlying rule.

Run with: streamlit run grokking_app.py
"""

import streamlit as st
import numpy as np
from scipy import ndimage
from dataclasses import dataclass
from typing import List, Tuple, Dict
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# Page configuration
st.set_page_config(
    page_title="SGC Grokking Visualizer",
    page_icon="🧠",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS
st.markdown("""
<style>
    .stApp {
        background-color: #0a0a0f;
    }
    .phase-chaos {
        background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
        border: 2px solid #666;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
    }
    .phase-memorize {
        background: linear-gradient(135deg, #2e1a1a 0%, #3e1616 100%);
        border: 2px solid #ff4444;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
        animation: pulse-red 2s infinite;
    }
    .phase-grok {
        background: linear-gradient(135deg, #1a2e1a 0%, #163e16 100%);
        border: 2px solid #00ff88;
        border-radius: 10px;
        padding: 15px;
        text-align: center;
    }
    @keyframes pulse-red {
        0%, 100% { box-shadow: 0 0 10px #ff4444; }
        50% { box-shadow: 0 0 30px #ff4444; }
    }
    .header-grok {
        background: linear-gradient(90deg, #ff4444, #00d4ff, #00ff88);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        font-size: 2.5rem;
        font-weight: bold;
        text-align: center;
    }
    .metric-big {
        font-size: 3rem;
        font-weight: bold;
        text-align: center;
    }
    .warning-text {
        color: #ff4444;
        font-weight: bold;
    }
    .safe-text {
        color: #00ff88;
        font-weight: bold;
    }
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════════════════════
# GROKKING SIMULATOR
# ═══════════════════════════════════════════════════════════════════════════════

class GrokkingSimulator:
    """
    Simulates the evolution of a neural network weight matrix through
    the three phases of learning: Chaos → Memorization → Grokking.
    """
    
    def __init__(self, size: int = 64, seed: int = 42):
        self.size = size
        self.rng = np.random.default_rng(seed)
        
        # Phase boundaries
        self.chaos_end = 200
        self.memorize_end = 800
        self.total_epochs = 1000
        
        # Pre-generate the "true pattern" (what grokking discovers)
        self._generate_true_pattern()
        
        # Pre-generate spike locations for memorization phase
        self._generate_spike_locations()
    
    def _generate_true_pattern(self):
        """Generate the 'ground truth' harmonic pattern."""
        x = np.linspace(0, 2 * np.pi, self.size)
        y = np.linspace(0, 2 * np.pi, self.size)
        X, Y = np.meshgrid(x, y)
        
        # Beautiful harmonic pattern (what the network "discovers")
        self.true_pattern = (
            0.3 * np.sin(X) * np.cos(Y) +
            0.2 * np.sin(2 * X + Y) +
            0.15 * np.cos(X - 2 * Y) +
            0.1 * np.sin(3 * X) * np.sin(3 * Y)
        )
        self.true_pattern = (self.true_pattern - self.true_pattern.min())
        self.true_pattern = self.true_pattern / self.true_pattern.max()
    
    def _generate_spike_locations(self):
        """Generate random spike locations for memorization phase."""
        n_spikes = 50
        self.spike_locs = [
            (self.rng.integers(5, self.size - 5),
             self.rng.integers(5, self.size - 5))
            for _ in range(n_spikes)
        ]
    
    def get_weights(self, epoch: int) -> np.ndarray:
        """Get the weight matrix at a given epoch."""
        epoch = max(0, min(epoch, self.total_epochs))
        
        if epoch < self.chaos_end:
            return self._chaos_phase(epoch)
        elif epoch < self.memorize_end:
            return self._memorization_phase(epoch)
        else:
            return self._grokking_phase(epoch)
    
    def _chaos_phase(self, epoch: int) -> np.ndarray:
        """Phase 1: Random noise, gradually decreasing."""
        progress = epoch / self.chaos_end
        noise_scale = 1.0 - 0.5 * progress
        
        # Use epoch as seed for reproducibility
        rng = np.random.default_rng(epoch + 1000)
        noise = rng.standard_normal((self.size, self.size))
        noise = ndimage.gaussian_filter(noise, sigma=1)
        
        return noise * noise_scale
    
    def _memorization_phase(self, epoch: int) -> np.ndarray:
        """Phase 2: Low noise + high-frequency spikes (overfitting)."""
        progress = (epoch - self.chaos_end) / (self.memorize_end - self.chaos_end)
        
        # Base: smooth low-frequency pattern emerging
        base = self.true_pattern * 0.3 * progress
        
        # Add decreasing background noise
        rng = np.random.default_rng(epoch + 2000)
        noise = rng.standard_normal((self.size, self.size)) * 0.1 * (1 - progress * 0.5)
        noise = ndimage.gaussian_filter(noise, sigma=2)
        
        # Add SPIKES (the "memorization" artifacts)
        spikes = np.zeros((self.size, self.size))
        spike_intensity = 0.8 * (1 - progress * 0.3)  # Spikes persist!
        
        for i, (x, y) in enumerate(self.spike_locs):
            # Each spike has slightly different intensity
            intensity = spike_intensity * (0.7 + 0.3 * np.sin(i * 0.5))
            # Sharp Gaussian spike
            Y, X = np.ogrid[:self.size, :self.size]
            dist = np.sqrt((X - x)**2 + (Y - y)**2)
            spikes += intensity * np.exp(-dist**2 / 4)
        
        return base + noise + spikes
    
    def _grokking_phase(self, epoch: int) -> np.ndarray:
        """Phase 3: Spikes dissolve, true pattern emerges."""
        progress = (epoch - self.memorize_end) / (self.total_epochs - self.memorize_end)
        
        # Spikes rapidly dissolve
        spike_decay = np.exp(-5 * progress)
        
        # True pattern emerges
        pattern_strength = 1 - spike_decay
        
        # Compute remaining spikes
        spikes = np.zeros((self.size, self.size))
        for i, (x, y) in enumerate(self.spike_locs):
            intensity = 0.5 * spike_decay * (0.7 + 0.3 * np.sin(i * 0.5))
            Y, X = np.ogrid[:self.size, :self.size]
            dist = np.sqrt((X - x)**2 + (Y - y)**2)
            spikes += intensity * np.exp(-dist**2 / 4)
        
        return self.true_pattern * pattern_strength + spikes
    
    def get_loss(self, epoch: int) -> float:
        """Simulated training loss (drops early, standard metric)."""
        if epoch < self.chaos_end:
            # Loss drops quickly during chaos phase
            return 1.0 - 0.7 * (epoch / self.chaos_end)
        elif epoch < self.memorize_end:
            # Loss stays low during memorization (the trap!)
            progress = (epoch - self.chaos_end) / (self.memorize_end - self.chaos_end)
            return 0.3 - 0.15 * progress
        else:
            # Loss drops to near-zero after grokking
            progress = (epoch - self.memorize_end) / (self.total_epochs - self.memorize_end)
            return 0.15 * np.exp(-3 * progress)
    
    def get_phase(self, epoch: int) -> str:
        """Get current training phase."""
        if epoch < self.chaos_end:
            return "CHAOS"
        elif epoch < self.memorize_end:
            return "MEMORIZATION"
        else:
            return "GROKKING"


# ═══════════════════════════════════════════════════════════════════════════════
# SGC ANALYSIS (reused from app.py)
# ═══════════════════════════════════════════════════════════════════════════════

class HilbertMapper:
    """Hilbert curve mapping for locality-preserving 2D to 1D conversion."""
    
    def __init__(self, order: int):
        self.order = order
        self.size = 2 ** order
        self.n_points = self.size ** 2
        
        try:
            from hilbertcurve.hilbertcurve import HilbertCurve
            self.hc = HilbertCurve(order, 2)
        except ImportError:
            self.hc = None
    
    def index_to_point(self, d: int) -> Tuple[int, int]:
        if self.hc:
            point = self.hc.point_from_distance(d)
            return (point[0], point[1])
        return (d % self.size, d // self.size)
    
    def flatten_image(self, img: np.ndarray) -> np.ndarray:
        result = np.zeros(self.n_points)
        for d in range(self.n_points):
            x, y = self.index_to_point(d)
            if y < img.shape[0] and x < img.shape[1]:
                result[d] = img[y, x]
        return result
    
    def unflatten_image(self, data: np.ndarray) -> np.ndarray:
        result = np.zeros((self.size, self.size))
        for d in range(min(len(data), self.n_points)):
            x, y = self.index_to_point(d)
            result[y, x] = data[d]
        return result


class DiffusionWavelets:
    """Diffusion wavelet decomposition."""
    
    def __init__(self, n_scales: int = 5, t0: float = 1.0):
        self.n_scales = n_scales
        self.t0 = t0
    
    def heat_kernel_1d(self, signal: np.ndarray, t: float) -> np.ndarray:
        if t <= 0:
            return signal.copy()
        sigma = np.sqrt(2 * t)
        return ndimage.gaussian_filter1d(signal, sigma, mode='reflect')
    
    def wavelet_coefficients(self, signal: np.ndarray) -> List[np.ndarray]:
        coeffs = []
        prev_smooth = signal.copy()
        for j in range(self.n_scales):
            t_j = self.t0 * (2 ** j)
            curr_smooth = self.heat_kernel_1d(signal, t_j)
            wavelet = curr_smooth - prev_smooth
            coeffs.append(wavelet)
            prev_smooth = curr_smooth
        return coeffs


@dataclass
class SGCMetrics:
    """SGC analysis metrics."""
    stress_map: np.ndarray
    stress_score: float
    frame_tightness: float
    n_singularities: int


def analyze_weights(weights: np.ndarray, threshold: float = 0.4) -> SGCMetrics:
    """Run SGC analysis on weight matrix."""
    # Resize to power of 2
    size = weights.shape[0]
    order = int(np.log2(size))
    if 2 ** order != size:
        order = 6
        from PIL import Image
        img_pil = Image.fromarray((weights * 255).astype(np.uint8))
        img_pil = img_pil.resize((64, 64), Image.Resampling.LANCZOS)
        weights = np.array(img_pil) / 255.0
    
    # Normalize
    weights_norm = weights - weights.mean()
    if weights.std() > 0:
        weights_norm = weights_norm / weights.std()
    
    # Hilbert mapping
    mapper = HilbertMapper(order)
    signal_1d = mapper.flatten_image(weights_norm)
    
    # Wavelet decomposition
    wavelets = DiffusionWavelets(n_scales=4)
    coeffs = wavelets.wavelet_coefficients(signal_1d)
    
    # Compute stress
    stress_1d = np.zeros(len(signal_1d))
    for j, c in enumerate(coeffs):
        weight = 2.0 ** (len(coeffs) - j - 1)
        stress_1d += weight * np.abs(c)
    
    max_stress = np.max(stress_1d)
    if max_stress > 0:
        stress_1d = stress_1d / max_stress
    
    # Map back to 2D
    stress_2d = mapper.unflatten_image(stress_1d)
    
    # Metrics
    singularity_mask = stress_1d > threshold
    n_singularities = int(np.sum(singularity_mask))
    stress_score = np.mean(stress_1d[stress_1d > threshold]) if n_singularities > 0 else 0.0
    
    # Frame tightness
    total_energy = sum(np.sum(c**2) for c in coeffs)
    signal_energy = np.sum(signal_1d**2) + 1e-10
    frame_tightness = total_energy / signal_energy
    
    return SGCMetrics(
        stress_map=stress_2d,
        stress_score=stress_score,
        frame_tightness=frame_tightness,
        n_singularities=n_singularities
    )


# ═══════════════════════════════════════════════════════════════════════════════
# STREAMLIT UI
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    # Header
    st.markdown('<p class="header-grok">🧠 SGC Dynamics: The Grokking Phase Transition</p>', 
                unsafe_allow_html=True)
    st.markdown("""
    <div style="text-align: center; color: #888; margin-bottom: 20px;">
        <em>Revealing how Neural Networks shift from "Memorizing" to "Understanding"</em>
    </div>
    """, unsafe_allow_html=True)
    
    # Initialize simulator
    simulator = GrokkingSimulator(size=64, seed=42)
    
    # Sidebar
    with st.sidebar:
        st.header("🎛️ Training Controls")
        
        epoch = st.slider(
            "Training Epoch",
            min_value=0,
            max_value=1000,
            value=100,
            step=10,
            help="Drag to simulate training progress"
        )
        
        st.markdown("---")
        
        # Phase indicator
        phase = simulator.get_phase(epoch)
        if phase == "CHAOS":
            st.markdown('<div class="phase-chaos"><b>📡 PHASE: CHAOS</b><br>Random initialization</div>', 
                       unsafe_allow_html=True)
        elif phase == "MEMORIZATION":
            st.markdown('<div class="phase-memorize"><b>⚠️ PHASE: MEMORIZATION</b><br>Low Loss, High Stress!</div>', 
                       unsafe_allow_html=True)
        else:
            st.markdown('<div class="phase-grok"><b>✨ PHASE: GROKKING</b><br>True understanding achieved</div>', 
                       unsafe_allow_html=True)
        
        st.markdown("---")
        st.header("📖 Theory")
        
        st.markdown("""
        **The Grokking Phenomenon:**
        
        Neural networks can achieve low training loss 
        while still "memorizing" instead of "understanding."
        
        **SGC Detection:**
        
        - **Memorization** → High curvature geometry 
          (spiky, unstable weight landscape)
        
        - **Grokking** → Smooth harmonic geometry 
          (the network found the rule)
        
        **Key Insight:**
        
        Standard Loss is a *lie detector* that always 
        says "passed." SGC is the *polygraph* that 
        reveals the truth.
        """)
        
        st.markdown("---")
        st.markdown("[SGC Lean4 Library](https://github.com/JasonShroyer/sgc-lean)")
    
    # Get current state
    weights = simulator.get_weights(epoch)
    loss = simulator.get_loss(epoch)
    metrics = analyze_weights(weights)
    phase = simulator.get_phase(epoch)
    
    # Row 1: Metrics
    st.markdown("### 📊 Current Diagnostics")
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("Training Epoch", f"{epoch:,}")
    
    with col2:
        loss_delta = "LOW ✓" if loss < 0.3 else "HIGH"
        st.metric("Training Loss", f"{loss:.3f}", delta=loss_delta, 
                 delta_color="normal" if loss < 0.3 else "inverse")
    
    with col3:
        stress_status = "CRITICAL ⚠️" if metrics.stress_score > 0.3 else "STABLE ✓"
        st.metric("Geometric Stress", f"{metrics.stress_score:.3f}", 
                 delta=stress_status,
                 delta_color="inverse" if metrics.stress_score > 0.3 else "normal")
    
    with col4:
        tight_status = "PASS ✓" if metrics.frame_tightness < 1.5 else "FAIL"
        st.metric("Frame Tightness", f"{metrics.frame_tightness:.3f}",
                 delta=tight_status,
                 delta_color="normal" if metrics.frame_tightness < 1.5 else "inverse")
    
    # Warning banner for memorization phase
    if phase == "MEMORIZATION":
        st.error("""
        ⚠️ **DECEPTIVE REGIME DETECTED**  
        Loss appears low, but the network is **memorizing**, not **understanding**.  
        The weight geometry contains high-frequency singularities (overfitting artifacts).
        """)
    elif phase == "GROKKING":
        st.success("""
        ✨ **TRUE UNDERSTANDING ACHIEVED**  
        The network has undergone topological surgery. Weight geometry is now smooth and harmonic.
        """)
    
    st.markdown("---")
    
    # Row 2: Visualizations
    st.markdown("### 🔬 Weight Matrix Analysis")
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("**Weight Matrix Geometry**")
        fig1 = go.Figure(data=go.Heatmap(
            z=weights,
            colorscale='RdBu',
            zmid=0,
            showscale=True,
            colorbar=dict(title="Weight")
        ))
        fig1.update_layout(
            template='plotly_dark',
            height=400,
            margin=dict(l=20, r=20, t=20, b=20),
            xaxis=dict(showticklabels=False),
            yaxis=dict(showticklabels=False, scaleanchor='x')
        )
        st.plotly_chart(fig1, use_container_width=True)
    
    with col2:
        st.markdown("**SGC Stress Scan** (Singularity Detection)")
        fig2 = go.Figure(data=go.Heatmap(
            z=metrics.stress_map,
            colorscale='Hot',
            zmin=0,
            zmax=1,
            showscale=True,
            colorbar=dict(title="Stress")
        ))
        fig2.update_layout(
            template='plotly_dark',
            height=400,
            margin=dict(l=20, r=20, t=20, b=20),
            xaxis=dict(showticklabels=False),
            yaxis=dict(showticklabels=False, scaleanchor='x')
        )
        st.plotly_chart(fig2, use_container_width=True)
    
    st.markdown("---")
    
    # Row 3: The Seismograph
    st.markdown("### 📈 The Seismograph: Training Dynamics Over Time")
    
    # Generate full timeline data
    epochs = list(range(0, 1001, 10))
    losses = [simulator.get_loss(e) for e in epochs]
    stresses = []
    tightnesses = []
    
    for e in epochs:
        w = simulator.get_weights(e)
        m = analyze_weights(w)
        stresses.append(m.stress_score)
        tightnesses.append(min(m.frame_tightness, 2.0))  # Cap for display
    
    fig3 = make_subplots(rows=1, cols=1)
    
    # Loss trace
    fig3.add_trace(go.Scatter(
        x=epochs, y=losses,
        mode='lines',
        name='Training Loss',
        line=dict(color='#888888', width=2)
    ))
    
    # Stress trace
    fig3.add_trace(go.Scatter(
        x=epochs, y=stresses,
        mode='lines',
        name='Geometric Stress',
        line=dict(color='#ff4444', width=3)
    ))
    
    # Tightness trace
    fig3.add_trace(go.Scatter(
        x=epochs, y=[t / 2.0 for t in tightnesses],  # Normalize for display
        mode='lines',
        name='Frame Tightness (scaled)',
        line=dict(color='#00d4ff', width=2, dash='dot')
    ))
    
    # Current epoch marker
    fig3.add_vline(x=epoch, line_dash="dash", line_color="#00ff88", line_width=2,
                   annotation_text=f"Epoch {epoch}", annotation_position="top")
    
    # Phase regions
    fig3.add_vrect(x0=0, x1=200, fillcolor="#666666", opacity=0.1,
                   annotation_text="Chaos", annotation_position="top left")
    fig3.add_vrect(x0=200, x1=800, fillcolor="#ff4444", opacity=0.1,
                   annotation_text="Memorization (Danger Zone)", annotation_position="top left")
    fig3.add_vrect(x0=800, x1=1000, fillcolor="#00ff88", opacity=0.1,
                   annotation_text="Grokking", annotation_position="top left")
    
    fig3.update_layout(
        template='plotly_dark',
        height=350,
        margin=dict(l=50, r=50, t=30, b=50),
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="center", x=0.5),
        xaxis_title="Training Epoch",
        yaxis_title="Metric Value",
        yaxis=dict(range=[0, 1.1])
    )
    
    st.plotly_chart(fig3, use_container_width=True)
    
    # Interpretation
    st.markdown("---")
    st.markdown("### 🎯 Interpretation")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("""
        **What Standard Metrics Show:**
        - Loss drops early (Epoch ~200)
        - Model appears to have "learned"
        - Traditional ML would stop here ❌
        """)
    
    with col2:
        st.markdown("""
        **What SGC Reveals:**
        - Geometric Stress remains HIGH until Epoch ~800
        - Network is memorizing, not understanding
        - True grokking = geometric phase transition ✓
        """)
    
    # Footer
    st.markdown("---")
    st.markdown("""
    <div style="text-align: center; color: #666; font-size: 0.8rem;">
        <p>SGC Theory: Geometry = Stability | Curvature = Singularity</p>
        <p>Formally verified in <a href="https://github.com/JasonShroyer/sgc-lean" style="color: #00d4ff;">Lean4</a> | 
        Modules: SGC.Evolution.Dynamics, SGC.Thermodynamics.Evolution</p>
    </div>
    """, unsafe_allow_html=True)


if __name__ == "__main__":
    main()
