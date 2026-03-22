"""
SGC-THRML Demo: Basic Thermodynamic Computing with SGC Metrics

This demo shows:
1. Basic THRML Ising model sampling
2. Multi-basin energy landscape (functional blanket analog)
3. Temperature annealing (simulated grokking transition)
4. SGC metrics computed on THRML samples

Author: SGC Research Team
Date: February 6, 2026
"""

import jax
import jax.numpy as jnp
from typing import Tuple, List, Dict
import numpy as np

# THRML imports
try:
    from thrml import SpinNode, Block, SamplingSchedule, sample_states
    from thrml.models import IsingEBM, IsingSamplingProgram, hinton_init
    THRML_AVAILABLE = True
except ImportError as e:
    print(f"THRML not available: {e}")
    THRML_AVAILABLE = False


def demo_basic_ising_chain():
    """
    Demo 1: Basic Ising chain sampling.
    
    This is the simplest THRML example - a 1D chain of spins
    with ferromagnetic coupling.
    """
    print("\n" + "="*60)
    print("Demo 1: Basic Ising Chain Sampling")
    print("="*60)
    
    # Create a chain of 10 spin nodes
    n_spins = 10
    nodes = [SpinNode() for _ in range(n_spins)]
    
    # Connect adjacent spins (1D chain)
    edges = [(nodes[i], nodes[i+1]) for i in range(n_spins - 1)]
    
    # Parameters
    biases = jnp.zeros((n_spins,))        # No external field
    weights = jnp.ones((n_spins - 1,)) * 0.5  # Ferromagnetic coupling
    beta = jnp.array(1.0)                  # Inverse temperature
    
    # Create the Ising model
    model = IsingEBM(nodes, edges, biases, weights, beta)
    
    # Define sampling blocks (two-color for efficient Gibbs)
    # Even indices and odd indices can be updated in parallel
    free_blocks = [Block(nodes[::2]), Block(nodes[1::2])]
    
    # Create sampling program
    program = IsingSamplingProgram(model, free_blocks, clamped_blocks=[])
    
    # Initialize
    key = jax.random.key(42)
    k_init, k_samp = jax.random.split(key, 2)
    init_state = hinton_init(k_init, model, free_blocks, ())
    
    # Sampling schedule
    schedule = SamplingSchedule(n_warmup=100, n_samples=1000, steps_per_sample=2)
    
    # Run sampling
    samples = sample_states(k_samp, program, schedule, init_state, [], [Block(nodes)])
    
    # Analyze results
    samples_array = jnp.array(samples)
    mean_magnetization = jnp.mean(samples_array)
    correlation = jnp.mean(samples_array[:, 0] * samples_array[:, 1])
    
    print(f"Number of samples: {len(samples)}")
    print(f"Mean magnetization: {mean_magnetization:.3f}")
    print(f"Nearest-neighbor correlation: {correlation:.3f}")
    print(f"Sample shape: {samples_array.shape}")
    
    return samples_array


def demo_multi_basin_landscape():
    """
    Demo 2: Multi-basin energy landscape (Functional Blanket analog).
    
    Creates an Ising model with multiple energy minima,
    analogous to the "flat valleys with ridges" in SGC theory.
    """
    print("\n" + "="*60)
    print("Demo 2: Multi-Basin Energy Landscape")
    print("="*60)
    
    # Create a 2D grid of spins (4x4 = 16 spins)
    grid_size = 4
    n_spins = grid_size * grid_size
    nodes = [SpinNode() for _ in range(n_spins)]
    
    # Connect in a 2D grid pattern
    edges = []
    for i in range(grid_size):
        for j in range(grid_size):
            idx = i * grid_size + j
            # Horizontal edge
            if j < grid_size - 1:
                edges.append((nodes[idx], nodes[idx + 1]))
            # Vertical edge
            if i < grid_size - 1:
                edges.append((nodes[idx], nodes[idx + grid_size]))
    
    # Biases: create two "basins" by biasing half the grid each way
    biases = jnp.array([
        0.3 if (i // grid_size + i % grid_size) % 2 == 0 else -0.3
        for i in range(n_spins)
    ])
    
    # Weights: strong ferromagnetic coupling within basins
    weights = jnp.ones((len(edges),)) * 0.8
    
    # Low temperature to see basin structure
    beta = jnp.array(2.0)
    
    model = IsingEBM(nodes, edges, biases, weights, beta)
    
    # Two-color blocks for 2D grid
    even_nodes = [nodes[i] for i in range(n_spins) if (i // grid_size + i % grid_size) % 2 == 0]
    odd_nodes = [nodes[i] for i in range(n_spins) if (i // grid_size + i % grid_size) % 2 == 1]
    free_blocks = [Block(even_nodes), Block(odd_nodes)]
    
    program = IsingSamplingProgram(model, free_blocks, clamped_blocks=[])
    
    key = jax.random.key(123)
    k_init, k_samp = jax.random.split(key, 2)
    init_state = hinton_init(k_init, model, free_blocks, ())
    
    schedule = SamplingSchedule(n_warmup=200, n_samples=500, steps_per_sample=4)
    samples = sample_states(k_samp, program, schedule, init_state, [], [Block(nodes)])
    
    samples_array = jnp.array(samples)
    
    # Compute basin occupancy (how often each "class" is visited)
    # Class 0: mostly +1 spins, Class 1: mostly -1 spins
    magnetizations = jnp.mean(samples_array, axis=1)
    class_0 = jnp.sum(magnetizations > 0)
    class_1 = jnp.sum(magnetizations < 0)
    
    print(f"Grid size: {grid_size}x{grid_size} = {n_spins} spins")
    print(f"Number of edges: {len(edges)}")
    print(f"Inverse temperature beta: {beta}")
    print(f"Samples in Class 0 (M > 0): {class_0}")
    print(f"Samples in Class 1 (M < 0): {class_1}")
    print(f"Mean |magnetization|: {jnp.mean(jnp.abs(magnetizations)):.3f}")
    
    return samples_array, magnetizations


def demo_temperature_annealing():
    """
    Demo 3: Temperature annealing (simulated grokking transition).
    
    Shows how lowering temperature (increasing beta) causes
    the system to "crystallize" into a basin - analogous to grokking.
    """
    print("\n" + "="*60)
    print("Demo 3: Temperature Annealing (Grokking Analog)")
    print("="*60)
    
    # Simple 8-spin ring
    n_spins = 8
    nodes = [SpinNode() for _ in range(n_spins)]
    
    # Ring topology (periodic boundary)
    edges = [(nodes[i], nodes[(i+1) % n_spins]) for i in range(n_spins)]
    
    biases = jnp.zeros((n_spins,))
    weights = jnp.ones((n_spins,)) * 0.5  # Ferromagnetic
    
    # Annealing schedule: beta from 0.1 (hot) to 3.0 (cold)
    beta_schedule = [0.1, 0.3, 0.5, 1.0, 1.5, 2.0, 3.0]
    
    free_blocks = [Block(nodes[::2]), Block(nodes[1::2])]
    
    print("\nAnnealing Schedule:")
    print("-" * 50)
    print(f"{'Beta':>8} {'Temp':>8} {'|M|':>8} {'Var(M)':>10} {'Phase':>12}")
    print("-" * 50)
    
    results = []
    
    for beta_val in beta_schedule:
        beta = jnp.array(beta_val)
        model = IsingEBM(nodes, edges, biases, weights, beta)
        program = IsingSamplingProgram(model, free_blocks, clamped_blocks=[])
        
        key = jax.random.key(int(beta_val * 1000))
        k_init, k_samp = jax.random.split(key, 2)
        init_state = hinton_init(k_init, model, free_blocks, ())
        
        schedule = SamplingSchedule(n_warmup=100, n_samples=200, steps_per_sample=2)
        samples = sample_states(k_samp, program, schedule, init_state, [], [Block(nodes)])
        
        samples_array = jnp.array(samples)
        magnetizations = jnp.mean(samples_array, axis=1)
        
        mean_abs_m = jnp.mean(jnp.abs(magnetizations))
        var_m = jnp.var(magnetizations)
        temp = 1.0 / beta_val
        
        # Phase classification (SGC-style)
        if mean_abs_m < 0.3:
            phase = "EXPLORE"
        elif mean_abs_m < 0.7:
            phase = "TRANSITION"
        else:
            phase = "GROKKED"
        
        print(f"{beta_val:>8.1f} {temp:>8.2f} {mean_abs_m:>8.3f} {var_m:>10.4f} {phase:>12}")
        
        results.append({
            'beta': beta_val,
            'temp': temp,
            'mean_abs_m': float(mean_abs_m),
            'var_m': float(var_m),
            'phase': phase
        })
    
    print("-" * 50)
    print("\nInterpretation:")
    print("- High temp (low beta): System explores, |M| low (EXPLORE phase)")
    print("- Medium temp: System transitioning (TRANSITION phase)")
    print("- Low temp (high beta): System crystallizes, |M| high (GROKKED phase)")
    print("\nThis is the Kramers escape picture: lower temperature = deeper in basin")
    
    return results


def compute_sgc_metrics_thrml(samples: jnp.ndarray, class_labels: jnp.ndarray) -> Dict:
    """
    Compute SGC metrics from THRML samples.
    
    Args:
        samples: Array of spin configurations [n_samples, n_spins] or [1, n_samples, n_spins]
        class_labels: Class label for each sample
    
    Returns:
        Dictionary with functional_defect, ridge_ratio, etc.
    """
    # Handle THRML's output shape (may have extra batch dimension)
    if len(samples.shape) == 3:
        samples = samples[0]  # Remove batch dimension
    
    n_samples = len(samples)
    class_labels = jnp.array(class_labels).flatten()[:n_samples]
    
    unique_classes = jnp.unique(class_labels)
    n_classes = len(unique_classes)
    
    # Total variance
    total_var = jnp.var(samples)
    
    # Within-class variance (use numpy for boolean indexing)
    samples_np = np.array(samples)
    labels_np = np.array(class_labels)
    
    within_var = 0.0
    for c in np.unique(labels_np):
        mask = labels_np == c
        if np.sum(mask) > 1:
            class_samples = samples_np[mask]
            within_var += np.var(class_samples) * np.sum(mask)
    within_var = within_var / n_samples
    
    # Functional defect
    epsilon = within_var / (total_var + 1e-10)
    
    # Ridge ratio (simplified: use squared distance)
    E_within = 0.0
    E_between = 0.0
    n_within = 0
    n_between = 0
    
    # Sample pairs for efficiency (use numpy for compatibility)
    n_pairs = min(500, n_samples * (n_samples - 1) // 2)
    rng = np.random.default_rng(42)
    idx1 = rng.integers(0, n_samples, size=n_pairs)
    idx2 = rng.integers(0, n_samples, size=n_pairs)
    
    for i, j in zip(idx1, idx2):
        if i == j:
            continue
        # Convert to float for subtraction
        s_i = samples_np[i].astype(float)
        s_j = samples_np[j].astype(float)
        dist = np.sum((s_i - s_j)**2)
        if labels_np[i] == labels_np[j]:
            E_within += dist
            n_within += 1
        else:
            E_between += dist
            n_between += 1
    
    E_within = E_within / max(n_within, 1)
    E_between = E_between / max(n_between, 1)
    ridge_ratio = E_between / (E_within + 1e-10)
    
    return {
        'functional_defect': float(epsilon),
        'ridge_ratio': float(ridge_ratio),
        'total_variance': float(total_var),
        'within_variance': float(within_var),
        'n_classes': int(n_classes)
    }


def demo_sgc_metrics():
    """
    Demo 4: SGC metrics on THRML samples.
    
    Shows how to compute functional defect and ridge ratio
    from thermodynamic samples.
    """
    print("\n" + "="*60)
    print("Demo 4: SGC Metrics on THRML Samples")
    print("="*60)
    
    # Generate samples from multi-basin system
    samples_raw, magnetizations = demo_multi_basin_landscape()
    
    # Handle THRML output shape
    if len(samples_raw.shape) == 3:
        samples = samples_raw[0]  # Remove batch dim: [n_samples, n_spins]
    else:
        samples = samples_raw
    
    # Compute magnetization per sample and assign class labels
    sample_magnetizations = jnp.mean(samples, axis=1)
    class_labels = jnp.where(sample_magnetizations > 0, 0, 1)
    
    # Compute SGC metrics
    metrics = compute_sgc_metrics_thrml(samples, class_labels)
    
    print("\nSGC Metrics:")
    print("-" * 40)
    print(f"Functional Defect (epsilon): {metrics['functional_defect']:.4f}")
    print(f"Ridge Ratio (R):             {metrics['ridge_ratio']:.4f}")
    print(f"Total Variance:              {metrics['total_variance']:.4f}")
    print(f"Within-Class Variance:       {metrics['within_variance']:.4f}")
    print(f"Number of Classes:           {metrics['n_classes']}")
    print("-" * 40)
    
    # Interpret
    eps = metrics['functional_defect']
    R = metrics['ridge_ratio']
    
    if eps < 0.15 and R > 5:
        phase = "GROKKED - Sharp class boundaries, low within-class variance"
    elif eps < 0.5 or R > 1:
        phase = "TRANSITION - Some structure emerging"
    else:
        phase = "EXPLORE - No clear class structure"
    
    print(f"\nPhase Classification: {phase}")
    
    return metrics


# =============================================================================
# Main
# =============================================================================

if __name__ == "__main__":
    print("="*60)
    print("SGC-THRML Integration Demo")
    print("Thermodynamic Computing meets Spectral Graph Coarsening")
    print("="*60)
    
    if not THRML_AVAILABLE:
        print("\nERROR: THRML not installed. Run: pip install thrml")
        exit(1)
    
    # Run demos
    demo_basic_ising_chain()
    demo_temperature_annealing()
    demo_sgc_metrics()
    
    print("\n" + "="*60)
    print("Demo Complete!")
    print("="*60)
    print("\nKey Takeaways:")
    print("1. THRML provides native energy landscape computation")
    print("2. Temperature (beta) directly controls Kramers escape rate")
    print("3. SGC metrics (epsilon, R) can be computed from THRML samples")
    print("4. Multi-basin systems naturally encode functional blankets")
    print("\nNext: Port full grokking experiment to THRML")
    print("See: docs/SGC_THRML_INTEGRATION.md")
