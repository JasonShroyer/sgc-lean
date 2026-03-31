#!/usr/bin/env python3
"""
PERIHELION Stage 2: Wavelet Layer

Decomposes signals into:
- cA (approximation): slow pendulum dynamics
- cD (detail): sensor noise for thermal pump

Computes γ (spectral decay rate) and derives optimal n.

Formula: n = ceil(log(sqrt(N) / γ))
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass

try:
    import pywt
    PYWT_AVAILABLE = True
except ImportError:
    PYWT_AVAILABLE = False
    print("WARNING: PyWavelets not available. Using fallback decomposition.")


@dataclass
class WaveletDecomposition:
    """Result of wavelet decomposition."""
    cA: np.ndarray          # Approximation coefficients (slow dynamics)
    cD: np.ndarray          # Detail coefficients (noise)
    gamma: float            # Spectral decay rate
    optimal_n: int          # Derived representation depth
    energy_ratio: float     # cA energy / total energy


class WaveletLayer:
    """
    Stage 2 of PERIHELION pipeline.
    
    Separates scales via discrete wavelet transform:
    - cA captures the macroscopic reality (pendulum swing)
    - cD captures microscopic noise (sensor noise)
    
    Derives γ and optimal n from eigenspectrum.
    """
    
    def __init__(self, wavelet: str = 'db4', level: int = 1):
        """
        Initialize wavelet layer.
        
        Args:
            wavelet: Wavelet family (default 'db4' - Daubechies 4)
            level: Decomposition level
        """
        self.wavelet = wavelet
        self.level = level
        
        if not PYWT_AVAILABLE:
            print("Using numpy-based fallback for wavelet decomposition")
    
    def decompose(self, signal: np.ndarray) -> WaveletDecomposition:
        """
        Apply discrete wavelet transform to signal.
        
        Args:
            signal: 1D numpy array of signal values
            
        Returns:
            WaveletDecomposition with cA, cD, γ, optimal_n
        """
        if PYWT_AVAILABLE:
            return self._decompose_pywt(signal)
        else:
            return self._decompose_fallback(signal)
    
    def _decompose_pywt(self, signal: np.ndarray) -> WaveletDecomposition:
        """Decompose using PyWavelets."""
        # Single-level DWT
        cA, cD = pywt.dwt(signal, self.wavelet)
        
        # Compute spectral properties from cA
        gamma = self._compute_gamma(cA)
        
        # Derive optimal n from formula: n = ceil(log(sqrt(N) / γ))
        N = len(signal)
        if gamma > 0:
            optimal_n = max(1, int(np.ceil(np.log(np.sqrt(N) / gamma))))
        else:
            optimal_n = 1
        
        # Energy ratio
        total_energy = np.sum(cA**2) + np.sum(cD**2)
        cA_energy = np.sum(cA**2)
        energy_ratio = cA_energy / total_energy if total_energy > 0 else 0.5
        
        return WaveletDecomposition(
            cA=cA,
            cD=cD,
            gamma=gamma,
            optimal_n=optimal_n,
            energy_ratio=energy_ratio
        )
    
    def _decompose_fallback(self, signal: np.ndarray) -> WaveletDecomposition:
        """
        Fallback decomposition without PyWavelets.
        Uses simple moving average for low-pass and difference for high-pass.
        """
        n = len(signal)
        
        # Simple low-pass: average of pairs
        cA = np.array([(signal[2*i] + signal[2*i+1]) / np.sqrt(2) 
                       for i in range(n // 2)])
        
        # Simple high-pass: difference of pairs  
        cD = np.array([(signal[2*i] - signal[2*i+1]) / np.sqrt(2)
                       for i in range(n // 2)])
        
        # Compute gamma from cA
        gamma = self._compute_gamma(cA)
        
        # Optimal n
        if gamma > 0:
            optimal_n = max(1, int(np.ceil(np.log(np.sqrt(n) / gamma))))
        else:
            optimal_n = 1
        
        # Energy ratio
        total_energy = np.sum(cA**2) + np.sum(cD**2)
        cA_energy = np.sum(cA**2)
        energy_ratio = cA_energy / total_energy if total_energy > 0 else 0.5
        
        return WaveletDecomposition(
            cA=cA,
            cD=cD,
            gamma=gamma,
            optimal_n=optimal_n,
            energy_ratio=energy_ratio
        )
    
    def _compute_gamma(self, cA: np.ndarray) -> float:
        """
        Compute spectral decay rate γ from approximation coefficients.
        
        γ measures how fast the eigenspectrum decays.
        Higher γ = simpler signal (faster decay)
        Lower γ = more complex signal (slower decay)
        
        Uses power spectrum decay fitting.
        """
        if len(cA) < 4:
            return 1.0
        
        # Compute FFT and power spectrum
        fft = np.fft.fft(cA)
        power = np.abs(fft[:len(fft)//2])**2
        
        if len(power) < 2 or np.max(power) == 0:
            return 1.0
        
        # Normalize
        power = power / np.max(power)
        
        # Fit exponential decay: P(k) ~ exp(-γ * k)
        # Log-linear fit: log(P) = -γ * k + const
        k = np.arange(1, len(power))
        log_power = np.log(power[1:] + 1e-10)
        
        # Mask out zeros/negatives
        valid = log_power > -20
        if np.sum(valid) < 2:
            return 1.0
        
        k_valid = k[valid]
        log_p_valid = log_power[valid]
        
        # Linear regression for slope
        if len(k_valid) >= 2:
            slope, _ = np.polyfit(k_valid, log_p_valid, 1)
            gamma = -slope  # Decay rate (positive)
            return max(0.01, min(gamma, 10.0))  # Clamp to reasonable range
        
        return 1.0
    
    def multilevel_decompose(self, signal: np.ndarray, levels: int = None) -> Tuple[np.ndarray, list]:
        """
        Multi-level wavelet decomposition.
        
        Args:
            signal: Input signal
            levels: Number of levels (default: derived from γ)
            
        Returns:
            (final_cA, [cD_level1, cD_level2, ...])
        """
        # First decompose to get gamma and optimal_n
        decomp = self.decompose(signal)
        
        if levels is None:
            levels = min(decomp.optimal_n, int(np.log2(len(signal))) - 1)
        
        if not PYWT_AVAILABLE:
            # Fallback: return single-level
            return decomp.cA, [decomp.cD]
        
        # Multi-level decomposition
        coeffs = pywt.wavedec(signal, self.wavelet, level=levels)
        cA_final = coeffs[0]
        cDs = coeffs[1:]  # From coarsest to finest
        
        return cA_final, cDs


def test_wavelet_layer():
    """Quick test of wavelet layer."""
    print("Testing WaveletLayer...")
    
    # Generate test signal: pendulum-like oscillation + noise
    t = np.linspace(0, 10, 512)
    slow_dynamics = np.sin(2 * np.pi * 0.5 * t)  # 0.5 Hz oscillation
    noise = 0.1 * np.random.randn(len(t))
    signal = slow_dynamics + noise
    
    layer = WaveletLayer()
    decomp = layer.decompose(signal)
    
    print(f"  Signal length: {len(signal)}")
    print(f"  cA length: {len(decomp.cA)}")
    print(f"  cD length: {len(decomp.cD)}")
    print(f"  γ (spectral decay): {decomp.gamma:.4f}")
    print(f"  Optimal n: {decomp.optimal_n}")
    print(f"  Energy ratio (cA/total): {decomp.energy_ratio:.4f}")
    
    # Verify cA captures slow dynamics (should be smooth)
    cA_variance = np.var(np.diff(decomp.cA))
    cD_variance = np.var(decomp.cD)
    print(f"  cA smoothness (low = smooth): {cA_variance:.6f}")
    print(f"  cD variance (noise captured): {cD_variance:.6f}")
    
    assert decomp.energy_ratio > 0.8, "cA should capture most energy for clean signal"
    print("  ✓ Wavelet layer test passed")
    
    return decomp


if __name__ == "__main__":
    test_wavelet_layer()
