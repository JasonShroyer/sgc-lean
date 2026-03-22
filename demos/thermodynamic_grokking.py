"""
Thermodynamic Grokking & The Lifshitz Signature

This experiment tests whether grokking manifests as a literal second-order
phase transition on thermodynamic hardware, with a measurable signature
in specific heat (Cv) that aligns with functional defect collapse.

Author: SGC Research Team
Date: February 6, 2026
Experiment ID: THRML-001
"""

import jax
import jax.numpy as jnp
import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from datetime import datetime
import json
import os

# THRML imports
try:
    from thrml import SpinNode, Block, SamplingSchedule, sample_states
    from thrml.models import IsingEBM, IsingSamplingProgram, hinton_init
    THRML_AVAILABLE = True
except ImportError as e:
    print(f"THRML not available: {e}")
    THRML_AVAILABLE = False


# =============================================================================
# Spin Encoding
# =============================================================================

def encode_thermometer(value: int, p: int) -> List[int]:
    """
    Encode integer [0, p-1] as thermometer code.
    
    Example (p=7):
      0 -> [-1, -1, -1, -1, -1, -1]
      3 -> [+1, +1, +1, -1, -1, -1]
      6 -> [+1, +1, +1, +1, +1, +1]
    """
    return [+1 if i < value else -1 for i in range(p - 1)]


def decode_thermometer(spins: np.ndarray) -> int:
    """
    Decode thermometer code to integer.
    Counts consecutive +1s from the start.
    """
    count = 0
    for s in spins:
        if s > 0:  # +1
            count += 1
        else:
            break
    return count


def encode_sample(a: int, b: int, c: int, p: int) -> np.ndarray:
    """Encode (a, b, c) triple as spin configuration."""
    s_a = encode_thermometer(a, p)
    s_b = encode_thermometer(b, p)
    s_c = encode_thermometer(c, p)
    return np.array(s_a + s_b + s_c, dtype=np.float32)


def decode_sample(spins: np.ndarray, p: int) -> Tuple[int, int, int]:
    """Decode spin configuration to (a, b, c) triple."""
    n = p - 1
    s_a = spins[:n]
    s_b = spins[n:2*n]
    s_c = spins[2*n:3*n]
    return decode_thermometer(s_a), decode_thermometer(s_b), decode_thermometer(s_c)


# =============================================================================
# Energy Function
# =============================================================================

@dataclass
class ModularAdditionEnergy:
    """
    Energy function for modular addition task.
    
    E(s_a, s_b, s_c) = J_error * |c - (a+b) mod p| + J_struct * structure_penalty
    """
    p: int
    J_error: float = 2.0      # Penalty for wrong answer
    J_struct: float = 1.0     # Penalty for invalid thermometer codes
    
    def compute_energy(self, spins: np.ndarray) -> float:
        """Compute energy for a spin configuration."""
        a, b, c = decode_sample(spins, self.p)
        correct = (a + b) % self.p
        
        # Error energy: distance from correct answer
        error = min(abs(c - correct), self.p - abs(c - correct))  # Mod distance
        E_error = self.J_error * error
        
        # Structure penalty: invalid thermometer codes
        E_struct = self._structure_penalty(spins)
        
        return E_error + E_struct
    
    def _structure_penalty(self, spins: np.ndarray) -> float:
        """Penalize invalid thermometer patterns ([-1, +1] transitions)."""
        n = self.p - 1
        penalty = 0.0
        
        for start in [0, n, 2*n]:  # Each variable
            segment = spins[start:start+n]
            for i in range(len(segment) - 1):
                if segment[i] < 0 and segment[i+1] > 0:
                    penalty += self.J_struct
        
        return penalty
    
    def is_correct(self, spins: np.ndarray) -> bool:
        """Check if configuration gives correct answer."""
        a, b, c = decode_sample(spins, self.p)
        return c == (a + b) % self.p


# =============================================================================
# SGC Metrics
# =============================================================================

def compute_functional_defect(samples: np.ndarray, labels: np.ndarray) -> float:
    """
    Compute functional defect: within-class variance / total variance.
    
    Low epsilon = good class separation = grokked.
    """
    total_var = np.var(samples)
    if total_var < 1e-10:
        return 1.0
    
    within_var = 0.0
    n_samples = len(samples)
    
    for c in np.unique(labels):
        mask = labels == c
        if np.sum(mask) > 1:
            class_samples = samples[mask]
            within_var += np.var(class_samples) * np.sum(mask)
    
    within_var = within_var / n_samples
    return within_var / (total_var + 1e-10)


def compute_ridge_ratio(samples: np.ndarray, labels: np.ndarray, 
                        n_pairs: int = 500) -> float:
    """
    Compute ridge ratio: between-class distance / within-class distance.
    
    High R = sharp class boundaries = grokked.
    """
    n_samples = len(samples)
    if n_samples < 2:
        return 0.0
    
    rng = np.random.default_rng(42)
    idx1 = rng.integers(0, n_samples, size=n_pairs)
    idx2 = rng.integers(0, n_samples, size=n_pairs)
    
    E_within = 0.0
    E_between = 0.0
    n_within = 0
    n_between = 0
    
    for i, j in zip(idx1, idx2):
        if i == j:
            continue
        dist = np.sum((samples[i].astype(float) - samples[j].astype(float))**2)
        if labels[i] == labels[j]:
            E_within += dist
            n_within += 1
        else:
            E_between += dist
            n_between += 1
    
    E_within = E_within / max(n_within, 1)
    E_between = E_between / max(n_between, 1)
    
    return E_between / (E_within + 1e-10)


# =============================================================================
# Thermodynamic Measurements
# =============================================================================

def compute_specific_heat(energies: np.ndarray, beta: float) -> float:
    """
    Compute specific heat from energy samples.
    
    Cv = beta^2 * Var(E)
    """
    return beta**2 * np.var(energies)


def compute_binder_cumulant(energies: np.ndarray) -> float:
    """
    Compute Binder cumulant for phase transition detection.
    
    U4 = 1 - <E^4> / (3 * <E^2>^2)
    """
    E2 = np.mean(energies**2)
    E4 = np.mean(energies**4)
    if E2 < 1e-10:
        return 0.0
    return 1.0 - E4 / (3.0 * E2**2 + 1e-10)


# =============================================================================
# BangBang Controller (simplified from sgc_controller.py)
# =============================================================================

class BangBangController:
    """
    Bang-bang controller for thermodynamic grokking.
    
    Modulates inverse temperature beta based on SGC metrics.
    """
    
    def __init__(self):
        self.beta_explore = 0.3      # High temp (exploration)
        self.beta_transition = 1.0   # Critical temp
        self.beta_grokked = 3.0      # Low temp (consolidation)
        
        self.epsilon_high = 0.5
        self.epsilon_low = 0.15
        self.R_threshold = 1.0
        
        self.phase = "EXPLORE"
    
    def get_beta(self, epsilon: float, ridge_ratio: float) -> float:
        """Get beta value based on current metrics."""
        if epsilon > self.epsilon_high:
            self.phase = "EXPLORE"
            return self.beta_explore
        elif ridge_ratio > self.R_threshold or epsilon < self.epsilon_high:
            if epsilon < self.epsilon_low and ridge_ratio > 5.0:
                self.phase = "GROKKED"
                return self.beta_grokked
            else:
                self.phase = "TRANSITION"
                return self.beta_transition
        else:
            self.phase = "EXPLORE"
            return self.beta_explore


# =============================================================================
# THRML-based Experiment (using manual sampling for flexibility)
# =============================================================================

def run_thermodynamic_grokking_manual(
    p: int = 7,
    beta_range: Tuple[float, float] = (0.1, 5.0),
    n_beta_steps: int = 20,
    n_samples_per_beta: int = 1000,
    n_gibbs_steps: int = 100,
    seed: int = 42
) -> Dict:
    """
    Run thermodynamic grokking experiment with manual Gibbs sampling.
    
    This version doesn't require full THRML but implements the core algorithm.
    """
    print("\n" + "="*70)
    print("THERMODYNAMIC GROKKING EXPERIMENT")
    print(f"Task: Modular Addition mod {p}")
    print("="*70)
    
    rng = np.random.default_rng(seed)
    energy_fn = ModularAdditionEnergy(p)
    n_spins = 3 * (p - 1)
    
    # Generate all correct (a, b, c) pairs
    correct_samples = []
    for a in range(p):
        for b in range(p):
            c = (a + b) % p
            correct_samples.append(encode_sample(a, b, c, p))
    correct_samples = np.array(correct_samples)
    
    # Beta schedule
    betas = np.linspace(beta_range[0], beta_range[1], n_beta_steps)
    
    results = {
        'p': p,
        'betas': betas.tolist(),
        'mean_energy': [],
        'var_energy': [],
        'specific_heat': [],
        'binder_cumulant': [],
        'accuracy': [],
        'functional_defect': [],
        'ridge_ratio': [],
        'phase': []
    }
    
    controller = BangBangController()
    
    print(f"\n{'Beta':>8} {'Temp':>8} {'Cv':>10} {'Acc':>8} {'Eps':>8} {'R':>8} {'Phase':>12}")
    print("-" * 70)
    
    for beta in betas:
        # Initialize random spin configuration
        current_spins = rng.choice([-1, 1], size=n_spins).astype(float)
        
        # Collect samples via Gibbs sampling
        samples = []
        energies = []
        
        for step in range(n_samples_per_beta + n_gibbs_steps):
            # Single-spin Gibbs update
            for i in range(n_spins):
                # Compute energy for both spin values
                current_spins[i] = +1
                E_plus = energy_fn.compute_energy(current_spins)
                current_spins[i] = -1
                E_minus = energy_fn.compute_energy(current_spins)
                
                # Gibbs probability
                dE = E_plus - E_minus
                p_plus = 1.0 / (1.0 + np.exp(beta * dE))
                
                # Sample
                if rng.random() < p_plus:
                    current_spins[i] = +1
                else:
                    current_spins[i] = -1
            
            # Collect sample after warmup
            if step >= n_gibbs_steps:
                samples.append(current_spins.copy())
                energies.append(energy_fn.compute_energy(current_spins))
        
        samples = np.array(samples)
        energies = np.array(energies)
        
        # Compute accuracy
        correct = sum(1 for s in samples if energy_fn.is_correct(s))
        accuracy = correct / len(samples)
        
        # Compute thermodynamic quantities
        mean_E = np.mean(energies)
        var_E = np.var(energies)
        Cv = compute_specific_heat(energies, beta)
        U4 = compute_binder_cumulant(energies)
        
        # Compute SGC metrics
        # Labels: which correct answer would each sample give?
        labels = np.array([decode_sample(s, p)[2] for s in samples])
        epsilon = compute_functional_defect(samples, labels)
        R = compute_ridge_ratio(samples, labels)
        
        # Controller phase (for reference)
        _ = controller.get_beta(epsilon, R)
        phase = controller.phase
        
        # Store results
        results['mean_energy'].append(float(mean_E))
        results['var_energy'].append(float(var_E))
        results['specific_heat'].append(float(Cv))
        results['binder_cumulant'].append(float(U4))
        results['accuracy'].append(float(accuracy))
        results['functional_defect'].append(float(epsilon))
        results['ridge_ratio'].append(float(R))
        results['phase'].append(phase)
        
        temp = 1.0 / beta
        print(f"{beta:>8.2f} {temp:>8.3f} {Cv:>10.4f} {accuracy:>8.3f} "
              f"{epsilon:>8.4f} {R:>8.2f} {phase:>12}")
    
    print("-" * 70)
    
    return results


def run_thrml_experiment(
    p: int = 7,
    beta_range: Tuple[float, float] = (0.1, 3.0),
    n_beta_steps: int = 15,
    n_samples: int = 500,
    seed: int = 42
) -> Dict:
    """
    Run experiment using THRML library.
    
    Note: This requires careful setup of the IsingEBM to encode the 
    modular addition task. For initial testing, use run_thermodynamic_grokking_manual.
    """
    if not THRML_AVAILABLE:
        print("THRML not available, falling back to manual implementation")
        return run_thermodynamic_grokking_manual(
            p=p, beta_range=beta_range, n_beta_steps=n_beta_steps,
            n_samples_per_beta=n_samples, seed=seed
        )
    
    # For now, use manual implementation as THRML requires more complex setup
    # to properly encode the modular addition energy function
    return run_thermodynamic_grokking_manual(
        p=p, beta_range=beta_range, n_beta_steps=n_beta_steps,
        n_samples_per_beta=n_samples, seed=seed
    )


# =============================================================================
# Analysis and Visualization
# =============================================================================

def analyze_results(results: Dict) -> Dict:
    """
    Analyze experiment results for phase transition signatures.
    """
    betas = np.array(results['betas'])
    Cv = np.array(results['specific_heat'])
    epsilon = np.array(results['functional_defect'])
    accuracy = np.array(results['accuracy'])
    R = np.array(results['ridge_ratio'])
    
    analysis = {}
    
    # Find Cv peak
    Cv_peak_idx = np.argmax(Cv)
    analysis['Cv_peak_beta'] = betas[Cv_peak_idx]
    analysis['Cv_peak_value'] = Cv[Cv_peak_idx]
    
    # Find epsilon inflection (steepest descent)
    d_epsilon = np.diff(epsilon)
    epsilon_inflection_idx = np.argmin(d_epsilon) + 1
    analysis['epsilon_inflection_beta'] = betas[epsilon_inflection_idx]
    
    # Find accuracy threshold crossing (90%)
    acc_threshold_idx = np.argmax(accuracy > 0.9) if any(accuracy > 0.9) else -1
    analysis['accuracy_90_beta'] = betas[acc_threshold_idx] if acc_threshold_idx >= 0 else None
    
    # Check alignment
    if analysis['accuracy_90_beta'] is not None:
        alignment = abs(analysis['Cv_peak_beta'] - analysis['epsilon_inflection_beta'])
        analysis['Cv_epsilon_alignment'] = alignment
        analysis['aligned'] = alignment < (betas[1] - betas[0]) * 2  # Within 2 steps
    else:
        analysis['aligned'] = False
    
    return analysis


def print_analysis(results: Dict, analysis: Dict):
    """Print analysis summary."""
    print("\n" + "="*70)
    print("ANALYSIS: LIFSHITZ SIGNATURE DETECTION")
    print("="*70)
    
    print(f"\n1. Specific Heat Peak:")
    print(f"   - Peak at beta = {analysis['Cv_peak_beta']:.3f}")
    print(f"   - Peak value Cv = {analysis['Cv_peak_value']:.4f}")
    
    print(f"\n2. Functional Defect Inflection:")
    print(f"   - Steepest descent at beta = {analysis['epsilon_inflection_beta']:.3f}")
    
    if analysis['accuracy_90_beta'] is not None:
        print(f"\n3. Accuracy Threshold (90%):")
        print(f"   - Crossed at beta = {analysis['accuracy_90_beta']:.3f}")
    else:
        print(f"\n3. Accuracy Threshold (90%): NOT REACHED")
    
    print(f"\n4. Alignment Check:")
    if analysis['aligned']:
        print(f"   - SUCCESS: Cv peak aligns with epsilon inflection!")
        print(f"   - Alignment error: {analysis.get('Cv_epsilon_alignment', 'N/A'):.3f}")
    else:
        print(f"   - No clear alignment detected")
    
    # Final verdict
    print("\n" + "="*70)
    if analysis['aligned']:
        print("VERDICT: LIFSHITZ SIGNATURE DETECTED")
        print("Grokking appears to be a second-order phase transition!")
    else:
        print("VERDICT: SIGNATURE UNCLEAR")
        print("May need more samples or different parameters.")
    print("="*70)


def save_results(results: Dict, analysis: Dict, output_dir: str = "logs/thrml_grokking"):
    """Save results to JSON."""
    os.makedirs(output_dir, exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = os.path.join(output_dir, f"run_{timestamp}")
    os.makedirs(run_dir, exist_ok=True)
    
    # Save results
    with open(os.path.join(run_dir, "results.json"), "w") as f:
        json.dump(results, f, indent=2)
    
    # Save analysis
    # Convert numpy types for JSON serialization
    def convert_for_json(v):
        if isinstance(v, (np.floating, np.integer)):
            return float(v)
        elif isinstance(v, (np.bool_, bool)):
            return bool(v)
        else:
            return v
    
    analysis_json = {k: convert_for_json(v) for k, v in analysis.items()}
    with open(os.path.join(run_dir, "analysis.json"), "w") as f:
        json.dump(analysis_json, f, indent=2)
    
    print(f"\nResults saved to: {run_dir}")
    return run_dir


# =============================================================================
# Main
# =============================================================================

def main():
    """Run the thermodynamic grokking experiment."""
    print("\n" + "="*70)
    print("THERMODYNAMIC GROKKING & THE LIFSHITZ SIGNATURE")
    print("Experiment THRML-001")
    print("="*70)
    print("\nHypothesis: Grokking = Second-Order Phase Transition")
    print("Observable: Specific Heat peak aligns with Functional Defect collapse")
    print("="*70)
    
    # Run experiment
    results = run_thermodynamic_grokking_manual(
        p=7,                          # Modular arithmetic mod 7
        beta_range=(0.1, 4.0),        # Temperature range
        n_beta_steps=20,              # Number of temperature points
        n_samples_per_beta=500,       # Samples per temperature
        n_gibbs_steps=100,            # Warmup steps
        seed=42
    )
    
    # Analyze
    analysis = analyze_results(results)
    print_analysis(results, analysis)
    
    # Save
    run_dir = save_results(results, analysis)
    
    print("\n" + "="*70)
    print("EXPERIMENT COMPLETE")
    print("="*70)
    print("\nNext steps:")
    print("1. Examine logs/thrml_grokking/run_*/results.json")
    print("2. Plot Cv vs beta alongside epsilon vs beta")
    print("3. If aligned, compute critical exponents")
    print("4. Repeat with different p values for universality check")
    
    return results, analysis


if __name__ == "__main__":
    results, analysis = main()
