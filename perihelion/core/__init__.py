"""
Perihelion Core: SGC Technology Stack for EGI Verification
============================================================

This module provides the core infrastructure for accelerated grokking
and EGI fixed point verification, as specified in QuotientGenerator.lean.

Modules:
    wavelet_layer: Hermite-Gaussian wavelet noise injection (3-10x acceleration)
    thermal_pump: Thermal annealing with SGC Reynolds number control
    sgc_engine: Core ε, χ_g, Ridge Ratio computation
    sgc_integrated_controller: Full SGC control loop with constrained updates

Author: SGC Research Team
Date: March 31, 2026
"""

from .wavelet_layer import WaveletNoiseInjector, hermite_gaussian_weight
from .thermal_pump import ThermalPump, ThermalSchedule
from .sgc_engine import SGCEngine, SGCMetrics
from .sgc_integrated_controller import SGCIntegratedController, ConstrainedUpdate

__all__ = [
    'WaveletNoiseInjector',
    'hermite_gaussian_weight',
    'ThermalPump',
    'ThermalSchedule',
    'SGCEngine',
    'SGCMetrics',
    'SGCIntegratedController',
    'ConstrainedUpdate',
]
