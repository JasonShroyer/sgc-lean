#!/usr/bin/env python3
"""
PERIHELION Fix 3: Analytical Ground Truth for Wavelet cD Coefficients

Derive the expected δ (transitivity defect) for wavelet detail coefficients
from the wavelet filter's autocorrelation properties.

Key insight: Wavelet detail coefficients are NOT iid Gaussian even when
the input signal has iid Gaussian noise. The high-pass filter creates
correlations between adjacent cD coefficients.

For a Haar wavelet:
- cD[n] = (x[2n] - x[2n+1]) / sqrt(2)
- Adjacent cD coefficients share no samples → uncorrelated
- But for higher-order wavelets (db4, etc.), overlap creates correlation

For Daubechies-4 wavelet (db4):
- Filter length = 8
- Adjacent cD coefficients overlap by 6 samples
- This creates significant autocorrelation

The transitivity rate for correlated noise:
- If cD has autocorrelation ρ, then P(a~c | a~b, b~c) ≠ P(a~c)
- The correlation structure affects chain completion probability
"""

import numpy as np
import pywt
from typing import Tuple, Dict


def compute_wavelet_filter_autocorrelation(wavelet_name: str = 'db4') -> Dict:
    """
    Compute the autocorrelation properties of a wavelet's detail filter.
    
    Returns:
        Dict with filter properties and theoretical predictions
    """
    wavelet = pywt.Wavelet(wavelet_name)
    
    # High-pass (detail) filter coefficients
    dec_hi = np.array(wavelet.dec_hi)
    filter_length = len(dec_hi)
    
    # Autocorrelation of the detail filter
    # This determines correlation between adjacent cD coefficients
    autocorr = np.correlate(dec_hi, dec_hi, mode='full')
    autocorr = autocorr / autocorr[len(autocorr)//2]  # Normalize
    
    # For downsampled output (cD), adjacent coefficients are 2 samples apart
    # The overlap between filter applications determines correlation
    overlap = filter_length - 2  # Samples shared between adjacent cD
    
    # Theoretical correlation between adjacent cD for white noise input
    # ρ = sum(h[k] * h[k+2]) / sum(h[k]^2)
    if filter_length > 2:
        rho_adjacent = np.sum(dec_hi[:-2] * dec_hi[2:]) / np.sum(dec_hi**2)
    else:
        rho_adjacent = 0.0
    
    return {
        'wavelet': wavelet_name,
        'filter_length': filter_length,
        'filter_coeffs': dec_hi,
        'autocorrelation': autocorr,
        'overlap_samples': overlap,
        'rho_adjacent': rho_adjacent,
    }


def theoretical_delta_for_correlated_noise(rho: float, n_bins: int = 5) -> float:
    """
    Compute theoretical δ for noise with autocorrelation ρ.
    
    For discretized noise with n_bins:
    - P(bin_a = bin_c) depends on correlation structure
    - Transitivity rate = P(a~c | a~b, b~c)
    
    For independent noise: trans_rate = 1/n_bins (random matching)
    For perfectly correlated: trans_rate = 1.0 (always match)
    
    Interpolation: trans_rate ≈ 1/n_bins + (1 - 1/n_bins) * |ρ|^2
    
    Args:
        rho: Autocorrelation coefficient
        n_bins: Number of discretization bins
        
    Returns:
        Theoretical δ value
    """
    # Base transitivity for independent noise
    base_trans = 1.0 / n_bins
    
    # Correlation boost: higher |ρ| → more transitivity
    # The relationship is approximately quadratic in ρ
    # because trans_rate involves conditional probability over 2 steps
    correlation_boost = (1.0 - base_trans) * (rho ** 2)
    
    trans_rate = base_trans + correlation_boost
    delta = 1.0 - trans_rate
    
    return delta


def compute_empirical_cD_correlation(n_samples: int = 10000) -> Dict:
    """
    Empirically measure cD coefficient correlation from white noise input.
    """
    # Generate white noise
    np.random.seed(42)
    noise = np.random.randn(n_samples)
    
    # Apply wavelet decomposition
    cA, cD = pywt.dwt(noise, 'db4')
    
    # Measure autocorrelation of cD
    cD_centered = cD - np.mean(cD)
    autocorr_empirical = np.correlate(cD_centered[:100], cD_centered[:100], mode='full')
    autocorr_empirical = autocorr_empirical / autocorr_empirical[len(autocorr_empirical)//2]
    
    # Adjacent correlation (lag=1)
    if len(cD) > 1:
        rho_empirical = np.corrcoef(cD[:-1], cD[1:])[0, 1]
    else:
        rho_empirical = 0.0
    
    return {
        'n_samples': n_samples,
        'cD_length': len(cD),
        'cD_mean': np.mean(cD),
        'cD_std': np.std(cD),
        'rho_empirical': rho_empirical,
        'autocorr': autocorr_empirical[len(autocorr_empirical)//2:len(autocorr_empirical)//2+5]
    }


def derive_noise_correlation_ground_truth(wavelet_name: str = 'db4', n_bins: int = 5) -> Dict:
    """
    Derive the analytically correct ground truth δ for NOISE_CORRELATION.
    
    This replaces the ad-hoc adjustment with a principled derivation.
    
    Returns:
        Dict with theoretical predictions and empirical validation
    """
    # Get wavelet filter properties
    filter_props = compute_wavelet_filter_autocorrelation(wavelet_name)
    rho_theoretical = filter_props['rho_adjacent']
    
    # Get empirical measurement
    empirical = compute_empirical_cD_correlation()
    rho_empirical = empirical['rho_empirical']
    
    # Compute theoretical δ
    delta_theoretical = theoretical_delta_for_correlated_noise(rho_theoretical, n_bins)
    delta_from_empirical = theoretical_delta_for_correlated_noise(rho_empirical, n_bins)
    
    # For truly independent noise, δ = 1 - 1/n_bins
    delta_independent = 1.0 - 1.0/n_bins
    
    return {
        'wavelet': wavelet_name,
        'n_bins': n_bins,
        'rho_theoretical': rho_theoretical,
        'rho_empirical': rho_empirical,
        'delta_independent': delta_independent,
        'delta_theoretical': delta_theoretical,
        'delta_from_empirical': delta_from_empirical,
        'filter_length': filter_props['filter_length'],
    }


def print_noise_ground_truth_derivation():
    """Print the full derivation for documentation."""
    print("=" * 70)
    print("  NOISE_CORRELATION Ground Truth Derivation")
    print("=" * 70)
    
    result = derive_noise_correlation_ground_truth('db4', n_bins=5)
    
    print(f"\nWavelet: {result['wavelet']} (filter length: {result['filter_length']})")
    print(f"\nAutocorrelation coefficients:")
    print(f"  Theoretical (from filter): rho = {result['rho_theoretical']:.4f}")
    print(f"  Empirical (from simulation): rho = {result['rho_empirical']:.4f}")
    
    print(f"\nDelta predictions (n_bins={result['n_bins']}):")
    print(f"  If truly independent: delta = {result['delta_independent']:.4f}")
    print(f"  From theoretical rho: delta = {result['delta_theoretical']:.4f}")
    print(f"  From empirical rho: delta = {result['delta_from_empirical']:.4f}")
    
    print(f"\nRecommended ground truth: delta = {result['delta_from_empirical']:.4f}")
    print(f"  (Based on empirical autocorrelation of wavelet cD coefficients)")
    
    # Compare different wavelets
    print("\n" + "-" * 70)
    print("  Comparison across wavelets:")
    print("-" * 70)
    for wname in ['haar', 'db2', 'db4', 'db8', 'sym4']:
        try:
            r = derive_noise_correlation_ground_truth(wname, n_bins=5)
            print(f"  {wname:6s}: rho={r['rho_empirical']:.4f}, delta={r['delta_from_empirical']:.4f}")
        except Exception as e:
            print(f"  {wname:6s}: error - {e}")
    
    return result


if __name__ == "__main__":
    result = print_noise_ground_truth_derivation()
