#!/usr/bin/env python3
"""
PERIHELION Stage 6: Thermal Pump

Uses wavelet detail coefficients (cD) as ambient noise source
to drive exploration at the critical boundary.

Pump intensity peaks at δ_critical = 0.15 (percolation threshold)

The system self-regulates:
- LOUD at critical (δ≈0.15): Maximum exploration, edge of chaos
- QUIET at ordered (δ≈0.00): System converged, exploration not needed
- QUIET at disordered (δ≈0.50): Too much noise, exploration wasted

Physics: Critical phase has maximum susceptibility to perturbations.
Small pushes cause large avalanches. Exploration is most effective here.
"""

import numpy as np
from dataclasses import dataclass
from typing import Dict, List, Optional
from collections import deque


@dataclass
class PumpState:
    """Current state of the thermal pump."""
    intensity: float           # Current pump strength
    phase: str                 # ordered/critical/disordered
    distance_to_critical: float
    noise_energy: float        # Energy available from cD
    timestep: int


class ThermalPump:
    """
    Stage 6 of PERIHELION pipeline.
    
    The thermal pump acts as a biological heartbeat:
    - Uses ambient high-frequency noise (cD) to inject thermodynamic energy
    - Maximum intensity at critical phase (edge of chaos)
    - Drives exploration where it's most effective
    
    Self-regulation (Gaussian peaked at δ_critical):
    - Ordered phase (δ < 0.05): pump QUIET, system already converged
    - Critical phase (δ ≈ 0.15): pump LOUD, maximum susceptibility
    - Disordered phase (δ > 0.30): pump QUIET, exploration wasted
    """
    
    DELTA_CRITICAL = 0.15  # Target δ at critical phase
    
    def __init__(
        self,
        base_intensity: float = 1.0,
        smoothing_window: int = 10
    ):
        """
        Initialize thermal pump.
        
        Args:
            base_intensity: Base pump intensity multiplier
            smoothing_window: Window for smoothing intensity over time
        """
        self.base_intensity = base_intensity
        self.smoothing_window = smoothing_window
        
        # State tracking
        self._intensity_history: List[float] = []
        self._cD_buffer: deque = deque(maxlen=100)
        self._current_state: Optional[PumpState] = None
    
    # Width of Gaussian peak around critical point
    SIGMA_CRITICAL = 0.10  # Controls how sharply pump peaks at δ=0.15
    
    def compute_intensity(
        self,
        delta_measured: float,
        cD: np.ndarray = None,
        timestep: int = 0
    ) -> PumpState:
        """
        Compute pump intensity based on current δ and available noise.
        
        Intensity = base * exp(-((δ - δ_critical)/σ)²) * noise_energy
        
        Gaussian peaked at δ_critical = 0.15:
        - Maximum at critical (edge of chaos, maximum susceptibility)
        - Falls off toward ordered (δ→0) and disordered (δ→0.5)
        
        Args:
            delta_measured: Current measured δ
            cD: Wavelet detail coefficients (noise source)
            timestep: Current timestep
            
        Returns:
            PumpState with computed intensity
        """
        # Distance from critical point
        distance = abs(delta_measured - self.DELTA_CRITICAL)
        
        # Classify phase
        if delta_measured < 0.05:
            phase = "ordered"
        elif delta_measured < 0.30:
            phase = "critical"
        else:
            phase = "disordered"
        
        # Noise energy from cD
        if cD is not None and len(cD) > 0:
            noise_energy = np.sqrt(np.mean(cD**2))  # RMS
            self._cD_buffer.extend(cD.flatten())
        else:
            noise_energy = 1.0  # Default
        
        # Compute intensity: Gaussian peaked at δ_critical
        # Maximum exploration at critical phase (edge of chaos)
        # Quiet at ordered (converged) and disordered (exploration wasted)
        gaussian_factor = np.exp(-((delta_measured - self.DELTA_CRITICAL) / self.SIGMA_CRITICAL) ** 2)
        intensity = self.base_intensity * gaussian_factor * noise_energy
        
        # Smooth intensity
        self._intensity_history.append(intensity)
        if len(self._intensity_history) > self.smoothing_window:
            smoothed = np.mean(self._intensity_history[-self.smoothing_window:])
        else:
            smoothed = intensity
        
        state = PumpState(
            intensity=smoothed,
            phase=phase,
            distance_to_critical=distance,
            noise_energy=noise_energy,
            timestep=timestep
        )
        
        self._current_state = state
        return state
    
    def compute_multi_relation(
        self,
        deltas: Dict[str, float],
        cD: np.ndarray = None,
        timestep: int = 0
    ) -> Dict[str, PumpState]:
        """
        Compute pump intensity for multiple relations.
        
        Returns dict of relation -> PumpState
        """
        states = {}
        for relation, delta in deltas.items():
            states[relation] = self.compute_intensity(delta, cD, timestep)
        return states
    
    def get_exploration_noise(self, shape: tuple = None) -> np.ndarray:
        """
        Generate exploration noise based on current pump state.
        
        Uses accumulated cD as noise source.
        Scales by current intensity.
        """
        if self._current_state is None:
            intensity = 0.1
        else:
            intensity = self._current_state.intensity
        
        if shape is None:
            shape = (1,)
        
        # Use cD buffer if available
        if len(self._cD_buffer) >= np.prod(shape):
            noise = np.array(list(self._cD_buffer)[:np.prod(shape)])
            noise = noise.reshape(shape)
        else:
            noise = np.random.randn(*shape)
        
        return intensity * noise
    
    def get_intensity_history(self) -> List[float]:
        """Get history of pump intensities."""
        return self._intensity_history.copy()
    
    def is_at_critical(self, tolerance: float = 0.05) -> bool:
        """Check if system is at critical phase."""
        if self._current_state is None:
            return False
        return self._current_state.distance_to_critical < tolerance
    
    def reset(self):
        """Reset pump state."""
        self._intensity_history = []
        self._cD_buffer.clear()
        self._current_state = None


def test_thermal_pump():
    """Quick test of thermal pump."""
    print("Testing ThermalPump...")
    
    pump = ThermalPump(base_intensity=1.0)
    
    # Simulated cD noise
    cD = 0.1 * np.random.randn(50)
    
    # Test ordered phase (should have LOW intensity - system converged)
    state_ordered = pump.compute_intensity(delta_measured=0.02, cD=cD, timestep=0)
    print(f"  Ordered (delta=0.02):")
    print(f"    intensity: {state_ordered.intensity:.4f}")
    print(f"    phase: {state_ordered.phase}")
    
    # Test critical phase (should have HIGH intensity - edge of chaos)
    pump.reset()  # Reset to avoid smoothing effects
    state_critical = pump.compute_intensity(delta_measured=0.15, cD=cD, timestep=1)
    print(f"  Critical (delta=0.15):")
    print(f"    intensity: {state_critical.intensity:.4f}")
    print(f"    phase: {state_critical.phase}")
    
    # Test disordered phase (should have LOW intensity - exploration wasted)
    pump.reset()
    state_disordered = pump.compute_intensity(delta_measured=0.50, cD=cD, timestep=2)
    print(f"  Disordered (delta=0.50):")
    print(f"    intensity: {state_disordered.intensity:.4f}")
    print(f"    phase: {state_disordered.phase}")
    
    # Critical should have HIGHEST intensity (peak at edge of chaos)
    assert state_critical.intensity > state_ordered.intensity, \
        f"Critical {state_critical.intensity:.4f} should > Ordered {state_ordered.intensity:.4f}"
    assert state_critical.intensity > state_disordered.intensity, \
        f"Critical {state_critical.intensity:.4f} should > Disordered {state_disordered.intensity:.4f}"
    
    print("  [PASS] Thermal pump peaks at critical")
    
    # Print intensity curve
    print("\n  Intensity vs delta:")
    pump.reset()
    for delta in [0.00, 0.05, 0.10, 0.15, 0.20, 0.30, 0.40, 0.50]:
        pump.reset()
        state = pump.compute_intensity(delta_measured=delta, cD=cD, timestep=0)
        bar = "#" * int(state.intensity * 50)
        print(f"    delta={delta:.2f}: {state.intensity:.4f} {bar}")
    
    return pump


if __name__ == "__main__":
    test_thermal_pump()
