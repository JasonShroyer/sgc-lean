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
    topological_observables: b1 Betti number, Forman-Ricci curvature, Fermi quench
                             (ported from JAX/THRML experiments)

Author: SGC Research Team
Date: March 31, 2026
"""

from .wavelet_layer import WaveletNoiseInjector, hermite_gaussian_weight
from .thermal_pump import ThermalPump, ThermalSchedule
from .sgc_engine import SGCEngine, SGCMetrics
from .sgc_integrated_controller import SGCIntegratedController, ConstrainedUpdate
from .topological_observables import (
    compute_b1, compute_b1_torch,
    compute_forman_ricci, ricci_flow_step,
    fermi, fermi_quench_factor,
    compute_specific_heat, compute_binder_cumulant,
    compute_topological_metrics, TopologicalMetrics
)

__all__ = [
    'WaveletNoiseInjector',
    'hermite_gaussian_weight',
    'ThermalPump',
    'ThermalSchedule',
    'SGCEngine',
    'SGCMetrics',
    'SGCIntegratedController',
    'ConstrainedUpdate',
    # Topological observables (from JAX/THRML)
    'compute_b1',
    'compute_b1_torch',
    'compute_forman_ricci',
    'ricci_flow_step',
    'fermi',
    'fermi_quench_factor',
    'compute_specific_heat',
    'compute_binder_cumulant',
    'compute_topological_metrics',
    'TopologicalMetrics',
]
