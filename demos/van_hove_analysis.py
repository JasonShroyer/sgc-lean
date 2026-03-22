"""
Van Hove Singularity Analysis for Lifshitz Transition Paper

This script extracts the eigenvalue spectrum of the Sheaf Laplacian
at the blanket closure moment, demonstrating the d=3 critical dimension
of the Lifshitz transition.

Expected signatures:
- ρ(λ) ∝ √λ near zero (Van Hove singularity)  
- Exactly 3 eigenvalues crossing zero (d=3 critical manifold)
"""

import numpy as np
import json
import os
import sys

# Add demos directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from spiking_sheaf_engine import SpikingSheafEngine
from emergent_sheaf_engine import EmergentSheafAtlas


def collect_eigenvalue_spectra(max_tasks: int = 20, verbose: bool = True):
    """
    Run evaluation and collect eigenvalue spectra at blanket closure moments.
    """
    from eval_97_spiking import load_arc_tasks
    
    tasks = load_arc_tasks()[:max_tasks]
    atlas = EmergentSheafAtlas(signature_dims=16)
    
    all_spectra = []
    near_zero_counts = []
    
    for task_idx, task in enumerate(tasks):
        task_id = task.get('task_id', 'unknown')
        train_examples = task.get('train', [])
        
        # Reset shape mappings per task
        if hasattr(atlas, '_shape_mappings'):
            atlas._shape_mappings = []
        
        for ex in train_examples:
            inp = np.array(ex['input'], dtype=np.float32)
            out = np.array(ex['output'], dtype=np.float32)
            
            engine = SpikingSheafEngine(
                input_grid=inp,
                target_grid=out,
                atlas=atlas,
                spike_threshold=0.75,
                learning_rate=0.15
            )
            
            # Run inference and capture eigenvalue spectrum
            result = engine.thermodynamic_inference(
                max_iterations=100,
                verbose=False
            )
            
            history = result.get('history', {})
            spectrum = history.get('eigenvalue_spectrum')
            
            if spectrum is not None and len(spectrum) > 0:
                all_spectra.append(spectrum)
                n_near_zero = np.sum(np.abs(spectrum) < 0.1)
                near_zero_counts.append(n_near_zero)
                
                if verbose:
                    print(f"[{task_idx+1}/{len(tasks)}] {task_id}: "
                          f"{len(spectrum)} eigenvalues, {n_near_zero} near zero")
    
    return all_spectra, near_zero_counts


def analyze_van_hove_data(spectra, output_path: str = 'van_hove_data.json'):
    """
    Analyze and save the Van Hove singularity data.
    """
    # Combine all spectra
    all_eigenvalues = np.concatenate(spectra)
    
    # Focus on eigenvalues near zero (the critical region)
    near_zero_mask = np.abs(all_eigenvalues) < 1.0
    critical_eigenvalues = all_eigenvalues[near_zero_mask]
    
    # Compute histogram
    bins = np.linspace(0, 1.0, 50)
    counts, bin_edges = np.histogram(critical_eigenvalues, bins=bins, density=True)
    bin_centers = (bin_edges[:-1] + bin_edges[1:]) / 2
    
    # Fit: ρ(λ) = A * λ^α (expect α ≈ 0.5 for √λ)
    valid_mask = (bin_centers > 0.01) & (counts > 0)
    slope = None
    if np.any(valid_mask):
        log_centers = np.log(bin_centers[valid_mask])
        log_counts = np.log(counts[valid_mask] + 1e-10)
        coeffs = np.polyfit(log_centers, log_counts, 1)
        slope = coeffs[0]
    
    # Count near-zero eigenvalues per spectrum
    near_zero_per_spectrum = [int(np.sum(np.abs(s) < 0.1)) for s in spectra]
    unique_counts, count_freq = np.unique(near_zero_per_spectrum, return_counts=True)
    
    # Find mode (most common near-zero count)
    mode_near_zero = int(unique_counts[np.argmax(count_freq)])
    
    # Save data to JSON
    data = {
        'total_spectra': len(spectra),
        'total_eigenvalues': len(all_eigenvalues),
        'eigenvalues_near_zero': int(np.sum(np.abs(all_eigenvalues) < 0.1)),
        'mean_near_zero_per_spectrum': float(np.mean(near_zero_per_spectrum)),
        'mode_near_zero': mode_near_zero,
        'fitted_exponent': float(slope) if slope is not None else None,
        'expected_exponent': 0.5,
        'near_zero_distribution': {int(k): int(v) for k, v in zip(unique_counts, count_freq)},
        'histogram_bins': bin_centers.tolist(),
        'histogram_counts': counts.tolist()
    }
    
    with open(output_path, 'w') as f:
        json.dump(data, f, indent=2)
    print(f"Saved Van Hove data to: {output_path}")
    
    # Print summary statistics
    print("\n" + "="*60)
    print("VAN HOVE SINGULARITY ANALYSIS SUMMARY")
    print("="*60)
    print(f"Total spectra analyzed: {len(spectra)}")
    print(f"Total eigenvalues: {len(all_eigenvalues)}")
    print(f"Eigenvalues near zero (|λ| < 0.1): {np.sum(np.abs(all_eigenvalues) < 0.1)}")
    print(f"Mean near-zero count per spectrum: {np.mean(near_zero_per_spectrum):.2f}")
    print(f"Mode near-zero count: {mode_near_zero} (d=3 prediction)")
    if slope is not None:
        print(f"Fitted exponent: {slope:.3f} (expected: 0.5 for √λ)")
    print("="*60)
    
    return data


def main():
    print("="*60)
    print("VAN HOVE SINGULARITY ANALYSIS")
    print("Lifshitz Transition Critical Exponents")
    print("="*60)
    
    # Collect eigenvalue spectra
    spectra, near_zero_counts = collect_eigenvalue_spectra(max_tasks=30, verbose=True)
    
    if spectra:
        # Analyze and save data
        data = analyze_van_hove_data(spectra, output_path='van_hove_data.json')
    else:
        print("No eigenvalue spectra collected!")


if __name__ == '__main__':
    main()
