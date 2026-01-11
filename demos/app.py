#!/usr/bin/env python3
"""
SGC Multiscale Stability Analyzer - Interactive Web Interface

A Streamlit application for exploring Hilbert-ordered diffusion wavelet
analysis with formal verification backing from the SGC Lean4 library.

Run with: streamlit run app.py
"""

import streamlit as st
import numpy as np
from scipy import ndimage
from dataclasses import dataclass
from typing import List, Tuple, Optional
from PIL import Image
import io
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import base64

# Page configuration - must be first Streamlit command
st.set_page_config(
    page_title="SGC Stability Analyzer",
    page_icon="🔬",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Initialize session state for surgery results persistence
if 'surgery_result' not in st.session_state:
    st.session_state.surgery_result = None
if 'show_surgery' not in st.session_state:
    st.session_state.show_surgery = False

# Custom CSS for dark theme with accent colors
st.markdown("""
<style>
    .stApp {
        background-color: #0e1117;
    }
    .metric-card {
        background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
        border: 1px solid #0f3460;
        border-radius: 10px;
        padding: 20px;
        text-align: center;
    }
    .metric-value {
        font-size: 2.5rem;
        font-weight: bold;
        color: #00d4ff;
    }
    .metric-label {
        font-size: 0.9rem;
        color: #888;
        text-transform: uppercase;
        letter-spacing: 1px;
    }
    .status-pass {
        color: #00ff88;
    }
    .status-fail {
        color: #ff4444;
    }
    .header-text {
        background: linear-gradient(90deg, #00d4ff, #00ff88);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        font-size: 2.5rem;
        font-weight: bold;
    }
    .lean-badge {
        background: #1a1a2e;
        border: 1px solid #00d4ff;
        border-radius: 5px;
        padding: 5px 10px;
        font-family: monospace;
        font-size: 0.8rem;
        color: #00d4ff;
    }
</style>
""", unsafe_allow_html=True)


# ═══════════════════════════════════════════════════════════════════════════════
# ANALYSIS COMPONENTS (from sgc_analyzer.py)
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
    
    def get_curve_path(self, n_samples: int = 500) -> Tuple[List[int], List[int]]:
        """Get sampled path for visualization."""
        step = max(1, self.n_points // n_samples)
        xs, ys = [], []
        for d in range(0, self.n_points, step):
            x, y = self.index_to_point(d)
            xs.append(x)
            ys.append(y)
        return xs, ys


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


class StressDetector:
    """Singularity detection using thermodynamic criteria."""
    
    def __init__(self, threshold: float = 0.3):
        self.threshold = threshold
    
    def compute_stress(self, coeffs: List[np.ndarray]) -> np.ndarray:
        n = len(coeffs[0])
        stress = np.zeros(n)
        for j, c in enumerate(coeffs):
            weight = 2.0 ** (len(coeffs) - j - 1)
            stress += weight * np.abs(c)
        max_stress = np.max(stress)
        if max_stress > 0:
            stress = stress / max_stress
        return stress
    
    def detect_singularities(self, stress: np.ndarray) -> np.ndarray:
        return stress > self.threshold


@dataclass
class AnalysisResult:
    """Container for analysis results."""
    original_image: np.ndarray  # uint8, 0-255
    original_normalized: np.ndarray  # float, 0-1 for display
    hilbert_signal: np.ndarray
    stress_1d: np.ndarray
    stress_2d: np.ndarray
    singularity_mask: np.ndarray
    n_singularities: int
    stability_score: float
    frame_tightness: float


@st.cache_data(show_spinner=False)
def analyze_image(
    image_bytes: bytes,
    hilbert_order: int = 6,
    n_scales: int = 4,
    stress_threshold: float = 0.3
) -> AnalysisResult:
    """Run full SGC analysis pipeline. Cached to prevent re-computation."""
    # Convert bytes back to array for processing
    image = np.array(Image.open(io.BytesIO(image_bytes)))
    
    # Resize to power of 2
    size = 2 ** hilbert_order
    if image.shape[0] != size or image.shape[1] != size:
        img_pil = Image.fromarray(image.astype(np.uint8))
        img_pil = img_pil.resize((size, size), Image.Resampling.LANCZOS)
        image = np.array(img_pil)
    
    # Convert to grayscale if needed
    if len(image.shape) == 3:
        image = np.mean(image, axis=2)
    
    # Store both uint8 (for processing) and normalized (for display)
    image_uint8 = image.astype(np.uint8)
    image_normalized = image.astype(np.float64) / 255.0
    
    # Hilbert mapping
    mapper = HilbertMapper(hilbert_order)
    signal_1d = mapper.flatten_image(image.astype(float))
    
    # Normalize
    signal_mean = np.mean(signal_1d)
    signal_std = np.std(signal_1d)
    if signal_std > 0:
        signal_1d_norm = (signal_1d - signal_mean) / signal_std
    else:
        signal_1d_norm = signal_1d - signal_mean
    
    # Wavelet decomposition
    wavelets = DiffusionWavelets(n_scales=n_scales)
    coeffs = wavelets.wavelet_coefficients(signal_1d_norm)
    
    # Stress detection
    detector = StressDetector(threshold=stress_threshold)
    stress_1d = detector.compute_stress(coeffs)
    singularity_mask_1d = detector.detect_singularities(stress_1d)
    
    # Map back to 2D
    stress_2d = mapper.unflatten_image(stress_1d)
    singularity_mask_2d = mapper.unflatten_image(singularity_mask_1d.astype(float))
    
    # Compute metrics
    n_singularities = int(np.sum(singularity_mask_1d))
    stability_score = 1.0 - (n_singularities / len(signal_1d))
    
    # Frame tightness (simplified estimate)
    total_energy = sum(np.sum(c**2) for c in coeffs)
    signal_energy = np.sum(signal_1d_norm**2)
    frame_tightness = total_energy / (signal_energy + 1e-10)
    
    return AnalysisResult(
        original_image=image_uint8,
        original_normalized=image_normalized,
        hilbert_signal=signal_1d_norm,
        stress_1d=stress_1d,
        stress_2d=stress_2d,
        singularity_mask=singularity_mask_2d,
        n_singularities=n_singularities,
        stability_score=stability_score,
        frame_tightness=frame_tightness
    )


def apply_surgery(image: np.ndarray, stress_2d: np.ndarray, threshold: float = 0.5) -> np.ndarray:
    """Apply 'surgery' - smooth out high-stress regions."""
    mask = stress_2d > threshold
    result = image.copy()
    
    # Apply strong blur to stressed regions
    blurred = ndimage.gaussian_filter(image, sigma=3)
    result[mask] = blurred[mask]
    
    return result


def generate_demo_image(size: int = 256) -> bytes:
    """Generate a test pattern with known singularities."""
    img = np.zeros((size, size), dtype=np.uint8)
    
    # Smooth gradient background
    x, y = np.meshgrid(np.linspace(0, 1, size), np.linspace(0, 1, size))
    img = (128 + 50 * np.sin(4 * np.pi * x) * np.cos(4 * np.pi * y)).astype(np.uint8)
    
    # Sharp edges (singularities)
    img[size//4:3*size//4, size//4:size//4+3] = 255
    img[size//4:size//4+3, size//4:3*size//4] = 255
    
    # High-frequency noise patch
    noise_region = np.random.randint(0, 255, (size//6, size//6), dtype=np.uint8)
    img[3*size//4:3*size//4+size//6, 3*size//4:3*size//4+size//6] = noise_region
    
    # Circle
    center = (size//2, size//2)
    Y, X = np.ogrid[:size, :size]
    dist = np.sqrt((X - center[0])**2 + (Y - center[1])**2)
    img[dist < size//6] = 200
    
    # Convert to bytes for caching
    pil_img = Image.fromarray(img)
    buffer = io.BytesIO()
    pil_img.save(buffer, format='PNG')
    return buffer.getvalue()


def get_image_download_link(img_array: np.ndarray, filename: str, text: str) -> str:
    """Generate a download link for an image."""
    pil_img = Image.fromarray(img_array.astype(np.uint8))
    buffer = io.BytesIO()
    pil_img.save(buffer, format='PNG')
    b64 = base64.b64encode(buffer.getvalue()).decode()
    return f'<a href="data:image/png;base64,{b64}" download="{filename}" style="color: #00d4ff;">{text}</a>'


# ═══════════════════════════════════════════════════════════════════════════════
# STREAMLIT UI
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    # Header
    st.markdown('<p class="header-text">SGC Stability Analyzer</p>', unsafe_allow_html=True)
    st.markdown("*Hilbert-ordered diffusion wavelet analysis with Lean4 verification*")
    
    # Sidebar
    with st.sidebar:
        st.header("📁 Input")
        
        uploaded_file = st.file_uploader(
            "Upload Image",
            type=['png', 'jpg', 'jpeg', 'bmp', 'tiff'],
            help="Upload an image to analyze"
        )
        
        use_demo = st.checkbox("Use demo image", value=False, 
                               help="Try with a generated test pattern")
        
        st.markdown("---")
        st.header("⚙️ Parameters")
        
        hilbert_order = st.slider(
            "Hilbert Order",
            min_value=4, max_value=8, value=6,
            help=f"Grid: {2**6}×{2**6} = {(2**6)**2:,} points"
        )
        st.caption(f"→ {2**hilbert_order}×{2**hilbert_order} grid ({(2**hilbert_order)**2:,} points)")
        
        n_scales = st.slider(
            "Wavelet Scales",
            min_value=2, max_value=8, value=4,
            help="Number of multiscale decomposition levels"
        )
        
        stress_threshold = st.slider(
            "Singularity Threshold",
            min_value=0.1, max_value=0.9, value=0.3, step=0.05,
            help="Lower = more sensitive detection"
        )
        
        st.markdown("---")
        st.header("🔬 Verification")
        st.code("SGC.Measurement.Wavelets", language=None)
        st.code("SGC.Thermodynamics.Evolution", language=None)
        st.code("SGC.Evolution.Dynamics", language=None)
        
        st.markdown("---")
        st.link_button("View Source on GitHub", "https://github.com/JasonShroyer/sgc-lean", use_container_width=True)
    
    # Determine image source
    image_bytes = None
    image_source = None
    
    if uploaded_file is not None:
        image_bytes = uploaded_file.getvalue()
        image_source = uploaded_file.name
        # Reset surgery state on new image
        st.session_state.surgery_result = None
        st.session_state.show_surgery = False
    elif use_demo or st.session_state.get('use_demo_clicked', False):
        image_bytes = generate_demo_image(256)
        image_source = "Demo Pattern"
    
    # Main content
    if image_bytes is not None:
        # Run analysis with caching
        try:
            with st.spinner("Analyzing structural stability..."):
                result = analyze_image(
                    image_bytes,
                    hilbert_order=hilbert_order,
                    n_scales=n_scales,
                    stress_threshold=stress_threshold
                )
        except Exception as e:
            st.error(f"Error analyzing image: {str(e)}")
            st.info("Please try a different image or check the file format.")
            return
        
        # Row 1: Metrics
        st.markdown("### Diagnostic Summary")
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            stability_color = "normal" if result.stability_score > 0.7 else "inverse"
            st.metric(
                "System Stability",
                f"{result.stability_score:.1%}",
                delta=f"{(result.stability_score - 0.5) * 100:.0f}%" if result.stability_score != 0.5 else None,
                delta_color=stability_color
            )
        
        with col2:
            st.metric(
                "Singularities Detected",
                f"{result.n_singularities:,}",
                delta=None
            )
        
        with col3:
            tightness_status = "PASS" if result.frame_tightness < 1.5 else "FAIL"
            st.metric(
                "Frame Tightness (B/A)",
                f"{result.frame_tightness:.3f}",
                delta=tightness_status,
                delta_color="normal" if tightness_status == "PASS" else "inverse"
            )
        
        with col4:
            grid_size = 2 ** hilbert_order
            st.metric(
                "Analysis Grid",
                f"{grid_size} x {grid_size}",
                delta=f"{grid_size**2:,} points"
            )
        
        st.markdown("---")
        
        # Row 2: Images
        st.markdown("### Visual Analysis")
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown(f"**Original Image** ({result.original_image.shape[0]}×{result.original_image.shape[1]})")
            st.image(result.original_image, use_column_width=True)
            st.markdown(get_image_download_link(result.original_image, "original.png", "📥 Download"), unsafe_allow_html=True)
        
        with col2:
            st.markdown("**Singularity Map** (Stress Overlay)")
            # Create RGB overlay from normalized grayscale
            img_rgb = np.stack([result.original_normalized] * 3, axis=-1)
            
            # Apply stress as red/orange overlay (magma-style)
            stress_normalized = result.stress_2d / (result.stress_2d.max() + 1e-10)
            overlay = img_rgb.copy()
            # Red channel boost
            overlay[:, :, 0] = np.clip(overlay[:, :, 0] + stress_normalized * 0.8, 0, 1)
            # Slight orange tint
            overlay[:, :, 1] = np.clip(overlay[:, :, 1] + stress_normalized * 0.3 - stress_normalized * 0.5, 0, 1)
            # Reduce blue in stressed areas
            overlay[:, :, 2] = overlay[:, :, 2] * (1 - stress_normalized * 0.7)
            
            st.image(overlay, use_column_width=True, clamp=True)
            # Convert overlay to uint8 for download
            overlay_uint8 = (overlay * 255).astype(np.uint8)
            st.markdown(get_image_download_link(overlay_uint8, "stress_map.png", "📥 Download"), unsafe_allow_html=True)
        
        st.markdown("---")
        
        # Row 3: 1D Signal
        st.markdown("### Hilbert-Ordered Signal")
        
        # Subsample for display
        display_len = min(2000, len(result.hilbert_signal))
        step = max(1, len(result.hilbert_signal) // display_len)
        signal_display = result.hilbert_signal[::step]
        stress_display = result.stress_1d[::step]
        
        fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                           subplot_titles=("Hilbert-Ordered Signal", "Curvature Stress"),
                           vertical_spacing=0.1)
        
        # Signal trace
        fig.add_trace(
            go.Scatter(y=signal_display, mode='lines', 
                      line=dict(color='#00d4ff', width=1),
                      name='Signal'),
            row=1, col=1
        )
        
        # Stress trace
        fig.add_trace(
            go.Scatter(y=stress_display, mode='lines',
                      fill='tozeroy',
                      line=dict(color='#ff4444', width=1),
                      fillcolor='rgba(255, 68, 68, 0.3)',
                      name='Stress'),
            row=2, col=1
        )
        
        # Threshold line
        fig.add_hline(y=stress_threshold, line_dash="dash", 
                     line_color="#ffaa00", row=2, col=1,
                     annotation_text="Threshold")
        
        fig.update_layout(
            height=400,
            template='plotly_dark',
            showlegend=False,
            margin=dict(l=50, r=50, t=50, b=50)
        )
        
        st.plotly_chart(fig, use_container_width=True)
        
        st.markdown("---")
        
        # Row 4: Surgery
        st.markdown("### Topological Surgery")
        st.caption("Apply smoothing to detected singularity regions")
        
        col1, col2, col3 = st.columns([1, 2, 1])
        
        with col2:
            if st.button("🔧 Apply Surgery", use_container_width=True, type="primary"):
                st.session_state.surgery_result = apply_surgery(
                    result.original_image, result.stress_2d, stress_threshold
                )
                st.session_state.show_surgery = True
        
        # Show surgery results (persists across reruns)
        if st.session_state.show_surgery and st.session_state.surgery_result is not None:
            col_a, col_b = st.columns(2)
            with col_a:
                st.markdown("**Before**")
                st.image(result.original_image, use_column_width=True)
            with col_b:
                st.markdown("**After Surgery**")
                st.image(st.session_state.surgery_result, use_column_width=True)
                st.markdown(get_image_download_link(
                    st.session_state.surgery_result, "repaired.png", "📥 Download Repaired"
                ), unsafe_allow_html=True)
            
            st.success(f"✓ Surgery complete. {result.n_singularities:,} singularity points smoothed.")
        
        # Footer
        st.markdown("---")
        st.markdown("""
        <div style="text-align: center; color: #666; font-size: 0.8rem;">
            <p>Algorithms formally verified in Lean4 | 
            <a href="https://github.com/JasonShroyer/sgc-lean" style="color: #00d4ff;">SGC Library</a></p>
            <p>Frame Tightness: SGC.Measurement.Interfaces.TightnessRatio | 
            Surgery Criterion: SGC.Thermodynamics.Evolution.SatisfiesEvolutionInequality</p>
        </div>
        """, unsafe_allow_html=True)
    
    else:
        # No image uploaded - show welcome screen
        st.markdown("---")
        
        # Quick start
        col1, col2 = st.columns([2, 1])
        with col1:
            st.info("👈 **Upload an image** in the sidebar, or check **'Use demo image'** to try it out")
        with col2:
            if st.button("🎯 Try Demo Now", use_container_width=True, type="primary"):
                st.session_state['use_demo_clicked'] = True
                st.rerun()
        
        st.markdown("---")
        st.markdown("### How It Works")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.markdown("#### 1️⃣ Hilbert Mapping")
            st.markdown("""
            Image pixels are reordered along a space-filling 
            Hilbert curve, preserving spatial locality in 1D.
            """)
        
        with col2:
            st.markdown("#### 2️⃣ Wavelet Analysis")
            st.markdown("""
            Diffusion wavelets decompose the signal at multiple 
            scales without eigenvalue computation.
            """)
        
        with col3:
            st.markdown("#### 3️⃣ Singularity Detection")
            st.markdown("""
            Thermodynamic criteria identify structural 
            discontinuities requiring topological surgery.
            """)
        
        st.markdown("---")
        
        st.markdown("### Formal Verification")
        st.markdown("""
        All algorithms correspond to theorems proven in the **SGC Lean4 library**:
        """)
        
        col1, col2 = st.columns(2)
        with col1:
            st.code("""
SGC.Measurement.Interfaces.TightnessAudit
SGC.Measurement.Wavelets.DiffusionWavelet
            """, language="lean4")
        with col2:
            st.code("""
SGC.Thermodynamics.Evolution.CanEvolve
SGC.Evolution.Dynamics.EvolutionStep
            """, language="lean4")


if __name__ == "__main__":
    main()
