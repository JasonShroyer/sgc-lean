"""
Thermal Pump: Annealing Schedule with SGC Reynolds Number Control
==================================================================

Implements thermal annealing driven by the SGC Reynolds number:
    Re_SGC = κ · T · λ_pump / ||∇ε||

The pump raises temperature when χ_g (susceptibility) peaks, assisting
Kramers escape from local minima. It lowers temperature when ε < threshold
to consolidate the grokked state.

THEORETICAL FOUNDATION:
    - Kramers escape rate: Γ ~ exp(-ΔE / kT)
    - At χ_g peak: system is at critical point, maximize T to assist escape
    - At ε < 0.05: system has grokked, quench to consolidate

Author: SGC Research Team
Date: March 31, 2026
"""

import math
from dataclasses import dataclass, field
from typing import List, Tuple, Optional
from enum import Enum


class ThermalPhase(Enum):
    """Thermal annealing phases."""
    HEAT = "heat"           # Raising temperature, accumulating exploration mass
    QUENCH = "quench"       # Lowering temperature, consolidating
    STABLE = "stable"       # At target temperature, monitoring


@dataclass
class ThermalSchedule:
    """Configuration for thermal annealing schedule."""
    T_initial: float = 1.0      # Initial temperature
    T_max: float = 5.0          # Maximum temperature during heating
    T_target: float = 0.1       # Target temperature after quench
    
    heat_rate: float = 0.1      # Temperature increase per epoch during heat
    quench_rate: float = 0.5    # Temperature decrease rate during quench
    
    chi_g_threshold: float = 0.8    # χ_g threshold for peak detection
    epsilon_threshold: float = 0.05  # ε threshold for grokking detection
    ridge_ratio_target: float = 1.0  # R ≈ 1 indicates stable fixed point
    
    min_heat_epochs: int = 100   # Minimum epochs before quench allowed
    max_heat_epochs: int = 10000  # Force quench after this many epochs


@dataclass
class ThermalPump:
    """
    Thermal annealing controller with SGC Reynolds number feedback.
    
    The pump adjusts temperature based on:
    - χ_g (susceptibility): raise T at peak to assist Kramers escape
    - ε (defect): lower T when grokked to consolidate
    - Re_SGC: overall stability indicator
    """
    
    schedule: ThermalSchedule = field(default_factory=ThermalSchedule)
    
    # Current state
    temperature: float = 1.0
    phase: ThermalPhase = ThermalPhase.HEAT
    epoch: int = 0
    heat_start_epoch: int = 0
    quench_start_epoch: int = -1
    
    # Observables
    chi_g: float = 0.0          # Current susceptibility
    epsilon: float = 1.0        # Current defect
    ridge_ratio: float = 0.0    # Current ridge ratio R
    grad_epsilon_norm: float = 1.0  # ||∇ε||
    
    # SGC Reynolds number
    kappa: float = 0.01         # Coupling coefficient from wavelet injector
    lambda_pump: float = 1.0    # Pump rate coefficient
    Re_SGC: float = 0.0         # Current Reynolds number
    
    # History for peak detection
    chi_g_history: List[Tuple[int, float]] = field(default_factory=list)
    epsilon_history: List[Tuple[int, float]] = field(default_factory=list)
    temperature_history: List[Tuple[int, float]] = field(default_factory=list)
    
    # Peak detection state
    chi_g_peak_detected: bool = False
    chi_g_peak_epoch: int = -1
    chi_g_peak_value: float = 0.0
    
    def __post_init__(self):
        self.temperature = self.schedule.T_initial
    
    def compute_reynolds_number(self) -> float:
        """
        Compute SGC Reynolds number: Re_SGC = κ · T · λ_pump / ||∇ε||
        
        High Re_SGC indicates turbulent (exploring) regime.
        Low Re_SGC indicates laminar (consolidating) regime.
        """
        if self.grad_epsilon_norm < 1e-10:
            return float('inf')
        
        self.Re_SGC = (self.kappa * self.temperature * self.lambda_pump) / self.grad_epsilon_norm
        return self.Re_SGC
    
    def detect_chi_g_peak(self) -> bool:
        """
        Detect if χ_g has peaked (susceptibility maximum).
        
        Peak detection uses a rolling window: χ_g is at peak if current value
        is higher than both recent past and the threshold.
        """
        if len(self.chi_g_history) < 10:
            return False
        
        recent = [v for _, v in self.chi_g_history[-10:]]
        current = self.chi_g
        
        # Peak if: current > threshold AND current > recent average AND declining
        above_threshold = current > self.schedule.chi_g_threshold
        above_average = current > sum(recent) / len(recent)
        
        # Check if declining (past peak)
        if len(self.chi_g_history) >= 3:
            last_three = [v for _, v in self.chi_g_history[-3:]]
            declining = last_three[-1] < last_three[-2] < last_three[-3]
        else:
            declining = False
        
        if above_threshold and declining and not self.chi_g_peak_detected:
            self.chi_g_peak_detected = True
            self.chi_g_peak_epoch = self.epoch
            self.chi_g_peak_value = max(recent)
            return True
        
        return False
    
    def should_quench(self) -> Tuple[bool, str]:
        """
        Determine if system should transition to quench phase.
        
        Returns:
            (should_quench, reason)
        """
        epochs_heating = self.epoch - self.heat_start_epoch
        
        # Force quench after max epochs
        if epochs_heating >= self.schedule.max_heat_epochs:
            return True, "MAX_HEAT_EPOCHS"
        
        # Don't quench before minimum epochs
        if epochs_heating < self.schedule.min_heat_epochs:
            return False, f"MIN_EPOCHS ({epochs_heating}/{self.schedule.min_heat_epochs})"
        
        # Quench if grokked: ε < threshold AND R ≈ 1
        grokked = (self.epsilon < self.schedule.epsilon_threshold and 
                   abs(self.ridge_ratio - self.schedule.ridge_ratio_target) < 0.2)
        if grokked:
            return True, f"GROKKED (ε={self.epsilon:.4f}, R={self.ridge_ratio:.2f})"
        
        # Quench if past χ_g peak and ε declining
        if self.chi_g_peak_detected:
            epochs_since_peak = self.epoch - self.chi_g_peak_epoch
            if epochs_since_peak > 50 and self.epsilon < 0.2:
                return True, f"POST_PEAK (epochs_since={epochs_since_peak}, ε={self.epsilon:.4f})"
        
        return False, "HEATING"
    
    def update(self, epsilon: float, chi_g: float, ridge_ratio: float,
               kappa: float = 0.01, grad_epsilon_norm: float = 1.0) -> float:
        """
        Update thermal pump with new measurements.
        
        Args:
            epsilon: Current defect
            chi_g: Current susceptibility
            ridge_ratio: Current ridge ratio R
            kappa: Coupling coefficient from wavelet injector
            grad_epsilon_norm: Gradient norm ||∇ε||
            
        Returns:
            Updated temperature
        """
        self.epoch += 1
        self.epsilon = epsilon
        self.chi_g = chi_g
        self.ridge_ratio = ridge_ratio
        self.kappa = kappa
        self.grad_epsilon_norm = grad_epsilon_norm
        
        # Track history
        self.chi_g_history.append((self.epoch, chi_g))
        self.epsilon_history.append((self.epoch, epsilon))
        self.temperature_history.append((self.epoch, self.temperature))
        
        # Limit history length
        max_history = 1000
        if len(self.chi_g_history) > max_history:
            self.chi_g_history = self.chi_g_history[-max_history:]
            self.epsilon_history = self.epsilon_history[-max_history:]
            self.temperature_history = self.temperature_history[-max_history:]
        
        # Compute Reynolds number
        self.compute_reynolds_number()
        
        # Phase-dependent temperature update
        if self.phase == ThermalPhase.HEAT:
            self._update_heat_phase()
        elif self.phase == ThermalPhase.QUENCH:
            self._update_quench_phase()
        elif self.phase == ThermalPhase.STABLE:
            self._update_stable_phase()
        
        return self.temperature
    
    def _update_heat_phase(self):
        """Update temperature during heating phase."""
        # Check for peak detection (raise T at peak)
        if self.detect_chi_g_peak():
            # Boost temperature at χ_g peak (Kramers assist)
            self.temperature = min(self.temperature * 1.5, self.schedule.T_max)
            print(f"[ThermalPump] chi_g PEAK at epoch {self.epoch}, T -> {self.temperature:.3f}")
        
        # Check for quench trigger
        should_quench, reason = self.should_quench()
        if should_quench:
            self.phase = ThermalPhase.QUENCH
            self.quench_start_epoch = self.epoch
            print(f"[ThermalPump] QUENCH triggered at epoch {self.epoch}: {reason}")
            return
        
        # Normal heating: gradual temperature increase
        self.temperature = min(
            self.temperature + self.schedule.heat_rate,
            self.schedule.T_max
        )
    
    def _update_quench_phase(self):
        """Update temperature during quenching phase."""
        # Exponential cooling toward target
        delta = self.temperature - self.schedule.T_target
        self.temperature = self.schedule.T_target + delta * (1 - self.schedule.quench_rate)
        
        # Transition to stable when close to target
        if abs(self.temperature - self.schedule.T_target) < 0.01:
            self.phase = ThermalPhase.STABLE
            print(f"[ThermalPump] STABLE at epoch {self.epoch}, T = {self.temperature:.4f}")
    
    def _update_stable_phase(self):
        """Update temperature during stable phase."""
        # Monitor for instability (ε rising)
        if len(self.epsilon_history) >= 10:
            recent = [v for _, v in self.epsilon_history[-10:]]
            if recent[-1] > recent[0] * 1.5 and recent[-1] > 0.1:
                # Instability detected, reheat
                self.phase = ThermalPhase.HEAT
                self.heat_start_epoch = self.epoch
                self.chi_g_peak_detected = False
                print(f"[ThermalPump] REHEAT at epoch {self.epoch} (instability detected)")
    
    def get_weight_decay(self, base_wd: float = 1.0) -> float:
        """
        Compute temperature-dependent weight decay.
        
        Higher T -> lower effective weight decay (more exploration)
        Lower T -> higher effective weight decay (consolidation)
        """
        if self.phase == ThermalPhase.HEAT:
            # Reduce weight decay during heating
            return base_wd * (self.schedule.T_target / self.temperature)
        elif self.phase == ThermalPhase.QUENCH:
            # Increase weight decay during quench
            return base_wd * 2.0
        else:
            return base_wd
    
    def get_status(self) -> dict:
        """Get current thermal pump status."""
        return {
            'epoch': self.epoch,
            'phase': self.phase.value,
            'temperature': self.temperature,
            'epsilon': self.epsilon,
            'chi_g': self.chi_g,
            'ridge_ratio': self.ridge_ratio,
            'Re_SGC': self.Re_SGC,
            'chi_g_peak_detected': self.chi_g_peak_detected,
            'chi_g_peak_epoch': self.chi_g_peak_epoch,
        }
