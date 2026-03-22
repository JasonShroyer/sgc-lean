"""
THRML-002: Thermodynamic Grokking with Corrected SGC Order Parameters

This experiment fixes the order parameter issue from THRML-001 by:
1. Using CONDITIONAL sampling P(c|a,b) instead of joint P(a,b,c)
2. Implementing proper intrinsic order parameters:
   - epsilon_H: Conditional entropy (H(C|a,b) / log(p))
   - epsilon_V: Conditional variance (Var(c|a,b) / Var_unif)
3. Running finite-size scaling across p in {5, 7, 11, 13}
4. Extracting three independent critical points: beta_Cv, beta_epsilon, beta_U4

FALSIFIABLE PREDICTION: These three critical points should align and tighten
as p increases. Systematic separation falsifies "grokking = phase transition."

Author: SGC Research Team
Date: February 6, 2026
Experiment ID: THRML-002
"""

import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from datetime import datetime
import json
import os
from scipy.stats import entropy as scipy_entropy


# =============================================================================
# Spin Encoding (same as v1)
# =============================================================================

def encode_thermometer(value: int, p: int) -> List[int]:
    """Encode integer [0, p-1] as thermometer code."""
    return [+1 if i < value else -1 for i in range(p - 1)]


def decode_thermometer(spins: np.ndarray) -> int:
    """Decode thermometer code to integer."""
    count = 0
    for s in spins:
        if s > 0:
            count += 1
        else:
            break
    return count


# =============================================================================
# Energy Function
# =============================================================================

@dataclass
class ModularArithmeticEnergy:
    """
    Energy function for modular arithmetic: c = op(a, b) mod p.
    
    Supports both addition and multiplication.
    Uses a HARD energy gap (not linear penalty) to create sharper ridges.
    """
    p: int
    operation: str = "add"     # "add" or "mul"
    J_error: float = 5.0       # Increased: sharper ridge
    J_struct: float = 2.0      # Increased: enforce valid codes
    use_hard_penalty: bool = True  # Use step function instead of linear
    
    def compute_energy_conditional(self, a: int, b: int, c_spins: np.ndarray) -> float:
        """
        Compute energy for output c_spins given clamped inputs (a, b).
        This is for conditional sampling P(c|a,b).
        """
        c = decode_thermometer(c_spins)
        correct = self.correct_answer(a, b)
        
        # Error energy - use hard penalty for sharper ridge
        if self.use_hard_penalty:
            # Step function: 0 if correct, J_error if wrong
            E_error = 0.0 if c == correct else self.J_error
        else:
            # Linear penalty based on distance
            error = min(abs(c - correct), self.p - abs(c - correct))
            E_error = self.J_error * error
        
        # Structure penalty for c spins only
        E_struct = self._structure_penalty_single(c_spins)
        
        return E_error + E_struct
    
    def _structure_penalty_single(self, spins: np.ndarray) -> float:
        """Penalize invalid thermometer patterns in a single variable."""
        penalty = 0.0
        for i in range(len(spins) - 1):
            if spins[i] < 0 and spins[i+1] > 0:
                penalty += self.J_struct
        return penalty
    
    def correct_answer(self, a: int, b: int) -> int:
        """Return the correct c for given (a, b)."""
        if self.operation == "add":
            return (a + b) % self.p
        elif self.operation == "mul":
            return (a * b) % self.p
        else:
            raise ValueError(f"Unknown operation: {self.operation}")


# =============================================================================
# Conditional Gibbs Sampler
# =============================================================================

class ConditionalGibbsSampler:
    """
    Samples P(c | a, b) by clamping input spins and running Gibbs on output.
    
    This is the key correction from THRML-001: we're doing INFERENCE,
    treating (a,b) as boundary conditions and sampling the output distribution.
    """
    
    def __init__(self, p: int, energy_fn: ModularArithmeticEnergy, seed: int = 42):
        self.p = p
        self.n_c_spins = p - 1
        self.energy_fn = energy_fn
        self.rng = np.random.default_rng(seed)
    
    def sample_c_given_ab(
        self, 
        a: int, 
        b: int, 
        beta: float, 
        n_samples: int = 100,
        n_warmup: int = 50,
        n_between: int = 5
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Sample P(c | a, b) at inverse temperature beta.
        
        Returns:
            c_values: Array of decoded c values
            energies: Array of energies for each sample
        """
        # Initialize random c spins
        c_spins = self.rng.choice([-1, 1], size=self.n_c_spins).astype(float)
        
        c_values = []
        energies = []
        
        total_steps = n_warmup + n_samples * n_between
        
        for step in range(total_steps):
            # Single-spin Gibbs update on c spins only
            for i in range(self.n_c_spins):
                # Compute energy for both spin values
                c_spins[i] = +1
                E_plus = self.energy_fn.compute_energy_conditional(a, b, c_spins)
                c_spins[i] = -1
                E_minus = self.energy_fn.compute_energy_conditional(a, b, c_spins)
                
                # Gibbs probability
                dE = E_plus - E_minus
                p_plus = 1.0 / (1.0 + np.exp(beta * dE))
                
                if self.rng.random() < p_plus:
                    c_spins[i] = +1
                else:
                    c_spins[i] = -1
            
            # Collect sample after warmup, every n_between steps
            if step >= n_warmup and (step - n_warmup) % n_between == 0:
                c = decode_thermometer(c_spins)
                E = self.energy_fn.compute_energy_conditional(a, b, c_spins)
                c_values.append(c)
                energies.append(E)
        
        return np.array(c_values), np.array(energies)


# =============================================================================
# SGC Order Parameters (CORRECTED)
# =============================================================================

def compute_conditional_entropy_order_param(
    sampler: ConditionalGibbsSampler,
    p: int,
    beta: float,
    n_samples_per_input: int = 50
) -> Tuple[float, float, Dict]:
    """
    Compute epsilon_H = E_{a,b}[H(C|a,b)] / log(p)
    
    This measures how deterministic the mapping has become.
    epsilon_H -> 0 means grokking (deterministic mapping).
    epsilon_H -> 1 means uniform random output.
    
    Also returns accuracy and per-input statistics.
    """
    conditional_entropies = []
    accuracies = []
    all_energies = []
    
    for a in range(p):
        for b in range(p):
            c_samples, energies = sampler.sample_c_given_ab(
                a, b, beta, n_samples=n_samples_per_input
            )
            all_energies.extend(energies)
            
            # Build empirical distribution P(c|a,b)
            counts = np.zeros(p)
            for c in c_samples:
                if 0 <= c < p:
                    counts[c] += 1
            
            # Normalize
            prob = counts / (counts.sum() + 1e-10)
            
            # Compute entropy H(C|a,b)
            H = scipy_entropy(prob + 1e-10, base=2)  # bits
            H_normalized = H / np.log2(p)  # normalize by max entropy
            conditional_entropies.append(H_normalized)
            
            # Compute accuracy for this (a,b)
            correct = sampler.energy_fn.correct_answer(a, b)
            acc = counts[correct] / (counts.sum() + 1e-10)
            accuracies.append(acc)
    
    epsilon_H = np.mean(conditional_entropies)
    accuracy = np.mean(accuracies)
    
    stats = {
        'all_energies': np.array(all_energies),
        'conditional_entropies': np.array(conditional_entropies),
        'per_input_accuracies': np.array(accuracies)
    }
    
    return epsilon_H, accuracy, stats


def compute_conditional_variance_order_param(
    sampler: ConditionalGibbsSampler,
    p: int,
    beta: float,
    n_samples_per_input: int = 50
) -> Tuple[float, float, Dict]:
    """
    Compute epsilon_V = E_{a,b}[Var(c|a,b)] / Var_unif
    
    Var_unif = variance of uniform distribution on {0, ..., p-1} = (p^2-1)/12
    
    epsilon_V -> 0 means grokking (all samples give same c).
    epsilon_V -> 1 means uniform random output.
    """
    var_unif = (p**2 - 1) / 12.0
    conditional_variances = []
    accuracies = []
    all_energies = []
    
    for a in range(p):
        for b in range(p):
            c_samples, energies = sampler.sample_c_given_ab(
                a, b, beta, n_samples=n_samples_per_input
            )
            all_energies.extend(energies)
            
            # Compute variance of c samples
            if len(c_samples) > 1:
                var_c = np.var(c_samples)
            else:
                var_c = 0.0
            
            conditional_variances.append(var_c / var_unif)
            
            # Compute accuracy
            correct = sampler.energy_fn.correct_answer(a, b)
            acc = np.mean(c_samples == correct)
            accuracies.append(acc)
    
    epsilon_V = np.mean(conditional_variances)
    accuracy = np.mean(accuracies)
    
    stats = {
        'all_energies': np.array(all_energies),
        'conditional_variances': np.array(conditional_variances),
        'per_input_accuracies': np.array(accuracies)
    }
    
    return epsilon_V, accuracy, stats


# =============================================================================
# Thermodynamic Quantities
# =============================================================================

def compute_specific_heat(energies: np.ndarray, beta: float) -> float:
    """Cv = beta^2 * Var(E)"""
    return beta**2 * np.var(energies)


def compute_binder_cumulant(energies: np.ndarray) -> float:
    """U4 = 1 - <E^4> / (3 * <E^2>^2)"""
    E2 = np.mean(energies**2)
    E4 = np.mean(energies**4)
    if E2 < 1e-10:
        return 0.0
    return 1.0 - E4 / (3.0 * E2**2 + 1e-10)


# =============================================================================
# Main Experiment
# =============================================================================

def run_thrml002_experiment(
    p: int = 7,
    beta_range: Tuple[float, float] = (0.1, 5.0),
    n_beta_steps: int = 25,
    n_samples_per_input: int = 50,
    seed: int = 42,
    verbose: bool = True,
    operation: str = "add"
) -> Dict:
    """
    Run THRML-002: Corrected thermodynamic grokking experiment.
    
    Uses conditional sampling P(c|a,b) and proper SGC order parameters.
    """
    if verbose:
        print(f"\n{'='*70}")
        print(f"THRML-002: Conditional Thermodynamic Grokking (p={p}, op={operation})")
        print(f"System size: N = 3*(p-1) = {3*(p-1)} spins")
        print(f"{'='*70}")
    
    energy_fn = ModularArithmeticEnergy(p, operation=operation)
    sampler = ConditionalGibbsSampler(p, energy_fn, seed=seed)
    
    betas = np.linspace(beta_range[0], beta_range[1], n_beta_steps)
    
    results = {
        'p': p,
        'operation': operation,
        'n_spins': 3 * (p - 1),
        'betas': betas.tolist(),
        'epsilon_H': [],      # Conditional entropy order param
        'epsilon_V': [],      # Conditional variance order param
        'accuracy': [],
        'mean_energy': [],
        'var_energy': [],
        'specific_heat': [],
        'binder_cumulant': []
    }
    
    if verbose:
        print(f"\n{'Beta':>6} {'Temp':>7} {'eps_H':>7} {'eps_V':>7} "
              f"{'Acc':>6} {'Cv':>8} {'U4':>7}")
        print("-" * 60)
    
    for beta in betas:
        # Compute epsilon_H (conditional entropy)
        epsilon_H, acc_H, stats_H = compute_conditional_entropy_order_param(
            sampler, p, beta, n_samples_per_input
        )
        
        # Compute epsilon_V (conditional variance) - reuse sampler state
        epsilon_V, acc_V, stats_V = compute_conditional_variance_order_param(
            sampler, p, beta, n_samples_per_input
        )
        
        # Average accuracy from both measurements
        accuracy = (acc_H + acc_V) / 2
        
        # Combine energies from both measurements
        all_energies = np.concatenate([stats_H['all_energies'], stats_V['all_energies']])
        
        # Thermodynamic quantities
        mean_E = np.mean(all_energies)
        var_E = np.var(all_energies)
        Cv = compute_specific_heat(all_energies, beta)
        U4 = compute_binder_cumulant(all_energies)
        
        # Store results
        results['epsilon_H'].append(float(epsilon_H))
        results['epsilon_V'].append(float(epsilon_V))
        results['accuracy'].append(float(accuracy))
        results['mean_energy'].append(float(mean_E))
        results['var_energy'].append(float(var_E))
        results['specific_heat'].append(float(Cv))
        results['binder_cumulant'].append(float(U4))
        
        if verbose:
            temp = 1.0 / beta
            print(f"{beta:>6.2f} {temp:>7.3f} {epsilon_H:>7.4f} {epsilon_V:>7.4f} "
                  f"{accuracy:>6.3f} {Cv:>8.3f} {U4:>7.4f}")
    
    if verbose:
        print("-" * 60)
    
    return results


def extract_critical_points(results: Dict) -> Dict:
    """
    Extract three independent critical point estimates:
    1. beta_Cv: argmax of specific heat
    2. beta_epsilon: max slope of epsilon_H decrease (inflection point)
    3. beta_U4: feature in Binder cumulant
    """
    betas = np.array(results['betas'])
    Cv = np.array(results['specific_heat'])
    epsilon_H = np.array(results['epsilon_H'])
    U4 = np.array(results['binder_cumulant'])
    
    critical = {}
    
    # 1. beta_Cv: argmax of specific heat
    Cv_peak_idx = np.argmax(Cv)
    critical['beta_Cv'] = betas[Cv_peak_idx]
    critical['Cv_max'] = Cv[Cv_peak_idx]
    
    # 2. beta_epsilon: steepest decrease in epsilon_H
    d_epsilon = np.diff(epsilon_H)
    epsilon_inflection_idx = np.argmin(d_epsilon) + 1
    critical['beta_epsilon'] = betas[epsilon_inflection_idx]
    critical['epsilon_slope_max'] = -d_epsilon[epsilon_inflection_idx - 1]
    
    # 3. beta_U4: steepest change in Binder cumulant
    d_U4 = np.abs(np.diff(U4))
    U4_feature_idx = np.argmax(d_U4) + 1
    critical['beta_U4'] = betas[U4_feature_idx]
    
    # Alignment check
    betas_c = [critical['beta_Cv'], critical['beta_epsilon'], critical['beta_U4']]
    critical['spread'] = max(betas_c) - min(betas_c)
    critical['mean_beta_c'] = np.mean(betas_c)
    critical['aligned'] = critical['spread'] < (betas[1] - betas[0]) * 3
    
    return critical


def run_finite_size_scaling(
    p_values: List[int] = [5, 7, 11, 13],
    beta_range: Tuple[float, float] = (0.1, 6.0),
    n_beta_steps: int = 30,
    n_samples_per_input: int = 40,
    seed: int = 42
) -> Dict:
    """
    Run finite-size scaling analysis across multiple p values.
    
    This tests the falsifiable prediction: critical points should align
    and tighten as p increases.
    """
    print("\n" + "="*70)
    print("THRML-002: FINITE-SIZE SCALING ANALYSIS")
    print("="*70)
    print(f"\nSystem sizes: p = {p_values}")
    print(f"Corresponding N = {[3*(p-1) for p in p_values]} spins")
    print("="*70)
    
    all_results = {}
    all_critical = {}
    
    for p in p_values:
        print(f"\n>>> Running p = {p} (N = {3*(p-1)} spins)...")
        
        results = run_thrml002_experiment(
            p=p,
            beta_range=beta_range,
            n_beta_steps=n_beta_steps,
            n_samples_per_input=n_samples_per_input,
            seed=seed,
            verbose=True
        )
        
        critical = extract_critical_points(results)
        
        all_results[p] = results
        all_critical[p] = critical
        
        print(f"\n   Critical points for p={p}:")
        print(f"   - beta_Cv     = {critical['beta_Cv']:.3f} (Cv_max = {critical['Cv_max']:.2f})")
        print(f"   - beta_epsilon = {critical['beta_epsilon']:.3f}")
        print(f"   - beta_U4     = {critical['beta_U4']:.3f}")
        print(f"   - Spread      = {critical['spread']:.3f}")
        print(f"   - Aligned     = {critical['aligned']}")
    
    # Summary
    print("\n" + "="*70)
    print("FINITE-SIZE SCALING SUMMARY")
    print("="*70)
    print(f"\n{'p':>4} {'N':>4} {'beta_Cv':>10} {'beta_eps':>10} {'beta_U4':>10} {'Spread':>8} {'Aligned':>8}")
    print("-" * 70)
    
    for p in p_values:
        c = all_critical[p]
        N = 3 * (p - 1)
        print(f"{p:>4} {N:>4} {c['beta_Cv']:>10.3f} {c['beta_epsilon']:>10.3f} "
              f"{c['beta_U4']:>10.3f} {c['spread']:>8.3f} {str(c['aligned']):>8}")
    
    # Check falsifiable prediction
    spreads = [all_critical[p]['spread'] for p in p_values]
    tightening = all(spreads[i] >= spreads[i+1] for i in range(len(spreads)-1))
    
    print("-" * 70)
    print(f"\nFALSIFIABLE PREDICTION CHECK:")
    print(f"  Spreads: {[f'{s:.3f}' for s in spreads]}")
    
    if tightening:
        print(f"  RESULT: Spreads are TIGHTENING as p increases -> CONSISTENT with SGC")
    else:
        print(f"  RESULT: Spreads NOT monotonically tightening -> NEEDS MORE DATA or FALSIFIED")
    
    return {
        'p_values': p_values,
        'results': {p: all_results[p] for p in p_values},
        'critical_points': {p: all_critical[p] for p in p_values},
        'spreads': spreads,
        'tightening': tightening
    }


def save_results(data: Dict, output_dir: str = "logs/thrml002"):
    """Save all results to JSON."""
    os.makedirs(output_dir, exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    run_dir = os.path.join(output_dir, f"run_{timestamp}")
    os.makedirs(run_dir, exist_ok=True)
    
    # Convert any remaining numpy types
    def convert(obj):
        if isinstance(obj, (np.integer, np.floating)):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, (np.bool_, bool)):
            return bool(obj)
        elif isinstance(obj, dict):
            return {k: convert(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert(v) for v in obj]
        return obj
    
    data_json = convert(data)
    
    with open(os.path.join(run_dir, "results.json"), "w") as f:
        json.dump(data_json, f, indent=2)
    
    print(f"\nResults saved to: {run_dir}")
    return run_dir


# =============================================================================
# Main
# =============================================================================

def run_high_resolution_sweep(
    p: int = 7,
    beta_range: Tuple[float, float] = (0.3, 2.0),
    n_beta_steps: int = 40,
    n_samples_per_input: int = 80,
    seed: int = 42
) -> Dict:
    """
    High-resolution sweep around the suspected critical point.
    """
    print("\n" + "="*70)
    print(f"THRML-002b: HIGH-RESOLUTION SWEEP (p={p})")
    print(f"Beta range: {beta_range}, Steps: {n_beta_steps}")
    print("="*70)
    
    results = run_thrml002_experiment(
        p=p,
        beta_range=beta_range,
        n_beta_steps=n_beta_steps,
        n_samples_per_input=n_samples_per_input,
        seed=seed,
        verbose=True
    )
    
    critical = extract_critical_points(results)
    
    print(f"\nHIGH-RESOLUTION CRITICAL POINTS:")
    print(f"  beta_Cv      = {critical['beta_Cv']:.4f} (Cv_max = {critical['Cv_max']:.3f})")
    print(f"  beta_epsilon = {critical['beta_epsilon']:.4f}")
    print(f"  beta_U4      = {critical['beta_U4']:.4f}")
    print(f"  Spread       = {critical['spread']:.4f}")
    print(f"  ALIGNED      = {critical['aligned']}")
    
    return {'results': results, 'critical': critical}


def compute_susceptibility(results: Dict) -> np.ndarray:
    """
    Compute susceptibility chi = -d(epsilon_H)/d(beta).
    
    This measures how sharply the order parameter responds to temperature.
    Peak in chi indicates the transition.
    """
    betas = np.array(results['betas'])
    epsilon_H = np.array(results['epsilon_H'])
    
    # Numerical derivative
    d_epsilon = np.gradient(epsilon_H, betas)
    chi = -d_epsilon  # Negative because epsilon decreases
    
    return chi


def run_comprehensive_scaling():
    """
    Run high-resolution sweeps for multiple p values and analyze scaling.
    """
    print("\n" + "="*70)
    print("THRML-002b: COMPREHENSIVE FINITE-SIZE SCALING")
    print("="*70)
    
    p_values = [5, 7, 11, 13]
    all_results = {}
    all_critical = {}
    
    for p in p_values:
        print(f"\n{'='*70}")
        print(f"Running high-resolution sweep for p={p} (N={3*(p-1)} spins)")
        print("="*70)
        
        # Adjust beta range based on p (larger p may need different range)
        if p <= 7:
            beta_range = (0.3, 2.5)
        else:
            beta_range = (0.2, 2.0)
        
        results = run_thrml002_experiment(
            p=p,
            beta_range=beta_range,
            n_beta_steps=35,
            n_samples_per_input=50,
            seed=42,
            verbose=True
        )
        
        # Compute susceptibility
        chi = compute_susceptibility(results)
        results['susceptibility'] = chi.tolist()
        
        # Extract critical points including susceptibility peak
        critical = extract_critical_points(results)
        
        # Add susceptibility-based critical point
        chi_peak_idx = np.argmax(chi)
        critical['beta_chi'] = results['betas'][chi_peak_idx]
        critical['chi_max'] = float(chi[chi_peak_idx])
        
        # Recompute spread including chi
        betas_c = [critical['beta_Cv'], critical['beta_epsilon'], critical['beta_chi']]
        critical['spread_3'] = max(betas_c) - min(betas_c)
        critical['mean_beta_c_3'] = np.mean(betas_c)
        
        all_results[p] = results
        all_critical[p] = critical
        
        print(f"\nCritical points for p={p}:")
        print(f"  beta_Cv   = {critical['beta_Cv']:.3f} (Cv_max = {critical['Cv_max']:.2f})")
        print(f"  beta_eps  = {critical['beta_epsilon']:.3f}")
        print(f"  beta_chi  = {critical['beta_chi']:.3f} (chi_max = {critical['chi_max']:.3f})")
        print(f"  Spread(3) = {critical['spread_3']:.3f}")
    
    # Summary table
    print("\n" + "="*70)
    print("FINITE-SIZE SCALING SUMMARY")
    print("="*70)
    print(f"\n{'p':>4} {'N':>4} {'beta_Cv':>9} {'beta_eps':>9} {'beta_chi':>9} "
          f"{'Spread':>8} {'Cv_max':>8} {'chi_max':>8}")
    print("-" * 75)
    
    for p in p_values:
        c = all_critical[p]
        N = 3 * (p - 1)
        print(f"{p:>4} {N:>4} {c['beta_Cv']:>9.3f} {c['beta_epsilon']:>9.3f} "
              f"{c['beta_chi']:>9.3f} {c['spread_3']:>8.3f} "
              f"{c['Cv_max']:>8.2f} {c['chi_max']:>8.3f}")
    
    print("-" * 75)
    
    # Analyze scaling
    spreads = [all_critical[p]['spread_3'] for p in p_values]
    beta_cvs = [all_critical[p]['beta_Cv'] for p in p_values]
    Cv_maxs = [all_critical[p]['Cv_max'] for p in p_values]
    
    print(f"\nSCALING ANALYSIS:")
    print(f"  Spreads:  {[f'{s:.3f}' for s in spreads]}")
    print(f"  beta_Cv:  {[f'{b:.3f}' for b in beta_cvs]}")
    print(f"  Cv_max:   {[f'{c:.2f}' for c in Cv_maxs]}")
    
    # Check if Cv_max grows with system size (expected for phase transition)
    Cv_growing = all(Cv_maxs[i] <= Cv_maxs[i+1] for i in range(len(Cv_maxs)-1))
    print(f"\n  Cv_max growing with N? {Cv_growing}")
    
    # Check if spreads are tightening
    spreads_tightening = spreads[-1] < spreads[0]
    print(f"  Spreads tightening?    {spreads_tightening}")
    
    return {
        'p_values': p_values,
        'results': {str(p): all_results[p] for p in p_values},
        'critical': {str(p): all_critical[p] for p in p_values},
        'scaling': {
            'spreads': spreads,
            'beta_cvs': beta_cvs,
            'Cv_maxs': Cv_maxs,
            'Cv_growing': Cv_growing,
            'spreads_tightening': spreads_tightening
        }
    }


def run_operation_comparison(p: int = 7):
    """
    Compare addition vs multiplication to test universality.
    """
    print("\n" + "="*70)
    print(f"UNIVERSALITY TEST: Addition vs Multiplication (p={p})")
    print("="*70)
    
    operations = ["add", "mul"]
    all_results = {}
    all_critical = {}
    
    for op in operations:
        print(f"\n>>> Running {op} operation...")
        
        results = run_thrml002_experiment(
            p=p,
            beta_range=(0.3, 2.5),
            n_beta_steps=30,
            n_samples_per_input=50,
            seed=42,
            verbose=True,
            operation=op
        )
        
        chi = compute_susceptibility(results)
        results['susceptibility'] = chi.tolist()
        
        critical = extract_critical_points(results)
        chi_peak_idx = np.argmax(chi)
        critical['beta_chi'] = results['betas'][chi_peak_idx]
        critical['chi_max'] = float(chi[chi_peak_idx])
        
        betas_c = [critical['beta_Cv'], critical['beta_epsilon'], critical['beta_chi']]
        critical['spread_3'] = max(betas_c) - min(betas_c)
        
        all_results[op] = results
        all_critical[op] = critical
        
        print(f"\nCritical points for {op}:")
        print(f"  beta_Cv   = {critical['beta_Cv']:.3f}")
        print(f"  beta_eps  = {critical['beta_epsilon']:.3f}")
        print(f"  beta_chi  = {critical['beta_chi']:.3f}")
        print(f"  Spread    = {critical['spread_3']:.3f}")
    
    # Summary comparison
    print("\n" + "="*70)
    print("UNIVERSALITY TEST SUMMARY")
    print("="*70)
    print(f"\n{'Op':>6} {'beta_Cv':>9} {'beta_eps':>9} {'beta_chi':>9} {'Spread':>8} {'Cv_max':>8}")
    print("-" * 55)
    
    for op in operations:
        c = all_critical[op]
        print(f"{op:>6} {c['beta_Cv']:>9.3f} {c['beta_epsilon']:>9.3f} "
              f"{c['beta_chi']:>9.3f} {c['spread_3']:>8.3f} {c['Cv_max']:>8.2f}")
    
    print("-" * 55)
    
    # Check if both operations show phase transition signature
    add_aligned = all_critical['add']['spread_3'] < 0.2
    mul_aligned = all_critical['mul']['spread_3'] < 0.2
    
    print(f"\nPhase transition signature:")
    print(f"  Addition:       {'YES' if add_aligned else 'WEAK'}")
    print(f"  Multiplication: {'YES' if mul_aligned else 'WEAK'}")
    
    if add_aligned and mul_aligned:
        print(f"\n*** UNIVERSALITY CONFIRMED ***")
        print(f"Both operations show aligned critical points!")
    
    return {'results': all_results, 'critical': all_critical}


def main():
    """Run the full THRML-002 experiment with finite-size scaling."""
    
    print("\n" + "="*70)
    print("THRML-002b: THERMODYNAMIC GROKKING - COMPREHENSIVE SCALING STUDY")
    print("="*70)
    print("\nOBJECTIVE: Test if critical points align across system sizes")
    print("METRICS: beta_Cv (specific heat), beta_eps (entropy), beta_chi (susceptibility)")
    print("="*70)
    
    # Run universality test (add vs mul)
    univ_results = run_operation_comparison(p=7)
    
    # Save results
    run_dir = save_results(univ_results, output_dir="logs/thrml002_universality")
    
    print("\n" + "="*70)
    print("EXPERIMENT COMPLETE")
    print("="*70)
    
    return univ_results


if __name__ == "__main__":
    results = main()
