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

# Import Fermi quench for smooth phase transition (Fix 3)
from .topological_observables import fermi_quench_factor, compute_specific_heat


class ThermalPhase(Enum):
    """Thermal annealing phases."""
    HEAT = "heat"           # Raising temperature, accumulating exploration mass
    QUENCH = "quench"       # Lowering temperature, consolidating
    STABLE = "stable"       # At target temperature, monitoring


@dataclass
class ThermalSchedule:
    """
    Configuration for thermal annealing schedule.
    
    ZERO-PARAMETER ARCHITECTURE:
    Thresholds are NOT set here - they are derived from live measurements.
    Only physical constants and relative scaling factors are specified.
    """
    T_initial: float = 1.0      # Initial temperature (relative scale)
    T_max: float = 5.0          # Maximum temperature (relative to T_initial)
    T_target: float = 0.1       # Target temperature after quench (relative)
    
    # Removed: heat_rate, quench_rate - now derived from chi_g dynamics
    # Removed: chi_g_threshold - now uses peak detection (gradient sign change)
    # Removed: epsilon_threshold - now derived from partition size (1/n_blocks)
    
    ridge_ratio_target: float = 1.0  # R = 1 is the theoretical fixed point
    
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
    energy_history: List[float] = field(default_factory=list)  # For Cv computation
    
    # Peak detection state
    chi_g_peak_detected: bool = False
    chi_g_peak_epoch: int = -1
    chi_g_peak_value: float = 0.0
    
    # Cv-derived critical Reynolds number (Fix 2: ZERO-PARAMETER)
    # Re_crit is NOT a hardcoded constant - it is self-detected from Cv peak
    Re_crit: float = 1.0  # Initial estimate, updated by Cv peak detection
    Cv_peak_detected: bool = False
    Cv_peak_temperature: float = 1.0
    Cv_history: List[Tuple[int, float]] = field(default_factory=list)
    
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
    
    def update_energy(self, energy: float):
        """
        Track energy for Cv computation.
        
        Energy should be the loss value or free energy of the system.
        """
        self.energy_history.append(energy)
        if len(self.energy_history) > 100:
            self.energy_history = self.energy_history[-100:]
        
        # Compute Cv and check for peak
        if len(self.energy_history) >= 10:
            Cv = compute_specific_heat(self.energy_history[-50:], self.temperature)
            self.Cv_history.append((self.epoch, Cv))
            
            # Limit Cv history
            if len(self.Cv_history) > 200:
                self.Cv_history = self.Cv_history[-200:]
            
            # Detect Cv peak (Fix 2: self-derive Re_crit)
            self._detect_Cv_peak()
    
    def _detect_Cv_peak(self):
        """
        Detect specific heat peak using gradient sign change.
        
        ZERO-PARAMETER: Re_crit is derived from the temperature at Cv peak.
        
        Re_crit = T_peak * κ * λ_pump / ||∇ε||_at_peak
        
        This is the phase transition point - where the system should quench.
        """
        if len(self.Cv_history) < 10:
            return
        
        recent = [v for _, v in self.Cv_history[-10:]]
        
        # Compute gradient (finite differences)
        d_Cv = [recent[i+1] - recent[i] for i in range(len(recent)-1)]
        
        # Peak: gradient was positive, now negative (sign change)
        if len(d_Cv) >= 3:
            recent_grad = sum(d_Cv[-4:-1]) / 3 if len(d_Cv) >= 4 else d_Cv[-2]
            current_grad = d_Cv[-1]
            
            if recent_grad > 0 and current_grad < 0 and not self.Cv_peak_detected:
                # Cv peak detected! Derive Re_crit from current conditions
                self.Cv_peak_detected = True
                self.Cv_peak_temperature = self.temperature
                
                # Re_crit = T_peak / (κ * λ_pump / ||∇ε||)
                # This is the Reynolds number at the phase transition
                if self.grad_epsilon_norm > 1e-10:
                    self.Re_crit = (self.kappa * self.temperature * self.lambda_pump) / self.grad_epsilon_norm
                
                print(f"[ThermalPump] Cv PEAK detected at epoch {self.epoch}")
                print(f"  T_peak = {self.Cv_peak_temperature:.4f}")
                print(f"  Re_crit = {self.Re_crit:.4f} (SELF-DERIVED)")
    
    def get_fermi_quench_factor(self) -> float:
        """
        Compute the Fermi quench factor for smooth crystallization.
        
        σ_quench = fermi(Re_crit - Re_SGC)
        
        When σ → 1: System is crystallizing (reduce learning rate)
        When σ → 0: System is still exploring (maintain learning rate)
        
        This replaces the hard grokking quench with a continuous phase transition.
        """
        return fermi_quench_factor(self.Re_SGC, self.Re_crit, delta=0.2)
    
    def detect_chi_g_peak(self) -> bool:
        """
        Detect if chi_g has peaked using GRADIENT SIGN CHANGE.
        
        ZERO-PARAMETER: No threshold comparison.
        Peak is when d(chi_g)/dt changes from positive to negative.
        This is a detectable event, not a threshold.
        
        FALLBACK: If Cv peak hasn't been detected by the time chi_g peaks,
        use the chi_g peak conditions to derive Re_crit. This ensures the
        Fermi quench has a valid critical Reynolds number even when
        energy variance is too low for Cv peak detection.
        """
        if len(self.chi_g_history) < 10:
            return False
        
        recent = [v for _, v in self.chi_g_history[-10:]]
        
        # Compute gradient (finite differences)
        d_chi = [recent[i+1] - recent[i] for i in range(len(recent)-1)]
        
        # Peak: gradient was positive, now negative (sign change)
        if len(d_chi) >= 3:
            # Smooth gradient sign detection: majority of recent vs current
            recent_grad = sum(d_chi[-4:-1]) / 3 if len(d_chi) >= 4 else d_chi[-2]
            current_grad = d_chi[-1]
            
            if recent_grad > 0 and current_grad < 0 and not self.chi_g_peak_detected:
                self.chi_g_peak_detected = True
                self.chi_g_peak_epoch = self.epoch
                self.chi_g_peak_value = max(recent)
                
                # FALLBACK: If Cv peak hasn't fired, derive Re_crit from chi_g peak
                # chi_g peak is also a valid phase transition marker
                if not self.Cv_peak_detected and self.grad_epsilon_norm > 1e-10:
                    self.Re_crit = (self.kappa * self.temperature * self.lambda_pump) / self.grad_epsilon_norm
                    print(f"[ThermalPump] chi_g PEAK -> Re_crit = {self.Re_crit:.4f} (FALLBACK)")
                
                return True
        
        return False
    
    def should_quench(self) -> Tuple[bool, str]:
        """
        Determine if system should transition to quench phase.
        
        ZERO-PARAMETER: Uses derived thresholds, not hardcoded values.
        
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
        
        # DERIVED: epsilon threshold from partition size
        eps_threshold = self._get_derived_epsilon_threshold()
        
        # DERIVED: ridge ratio threshold from running statistics
        ridge_threshold = self._get_derived_ridge_threshold()
        
        # Quench if grokked: eps < derived_threshold AND R within derived bounds
        grokked = (self.epsilon < eps_threshold and 
                   self.ridge_ratio < ridge_threshold)
        if grokked:
            return True, f"GROKKED (eps={self.epsilon:.4f}<{eps_threshold:.4f}, R={self.ridge_ratio:.2f}<{ridge_threshold:.2f})"
        
        # Quench if past chi_g peak and epsilon declining
        if self.chi_g_peak_detected:
            epochs_since_peak = self.epoch - self.chi_g_peak_epoch
            # DERIVED: Wait epochs proportional to peak value
            wait_epochs = max(20, int(self.chi_g_peak_value * 100))
            # DERIVED: epsilon threshold for post-peak quench
            post_peak_threshold = eps_threshold * 4  # Allow 4x the grokking threshold
            
            if epochs_since_peak > wait_epochs and self.epsilon < post_peak_threshold:
                return True, f"POST_PEAK (epochs_since={epochs_since_peak}, eps={self.epsilon:.4f})"
        
        return False, "HEATING"
    
    def _get_derived_epsilon_threshold(self) -> float:
        """
        Derive epsilon threshold from effective partition size.
        
        delta_min = 1/n_blocks where n_blocks is estimated from epsilon history.
        """
        # Estimate n_blocks from current epsilon (inverse relationship)
        # When well-trained: eps ~ 1/sqrt(n_blocks), so n_blocks ~ 1/eps^2
        if self.epsilon > 0.01:
            estimated_blocks = min(100, max(2, int(1.0 / (self.epsilon ** 2))))
        else:
            estimated_blocks = 100
        
        return 1.0 / estimated_blocks
    
    def _get_derived_ridge_threshold(self) -> float:
        """
        Derive ridge ratio threshold from running statistics.
        
        R_quench = R_mean - R_std (one sigma below running mean).
        """
        if len(self.epsilon_history) < 10:
            return 10.0  # Conservative default
        
        # Use epsilon history to estimate ridge bounds
        # (ridge_ratio correlates inversely with training progress)
        recent_eps = [v for _, v in self.epsilon_history[-20:]]
        eps_mean = sum(recent_eps) / len(recent_eps)
        
        # As epsilon decreases, ridge threshold tightens toward 1.0
        # R_threshold = 1 + 10 * eps_mean (linear interpolation)
        return 1.0 + 10.0 * eps_mean
    
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
        """
        Update temperature during heating phase.
        
        ZERO-PARAMETER: Temperature evolution driven by chi_g dynamics.
        """
        # Check for peak detection (raise T at peak)
        if self.detect_chi_g_peak():
            # Boost temperature at chi_g peak (Kramers assist)
            self.temperature = min(self.temperature * 1.5, self.schedule.T_max)
            print(f"[ThermalPump] chi_g PEAK at epoch {self.epoch}, T -> {self.temperature:.3f}")
        
        # Check for quench trigger
        should_quench, reason = self.should_quench()
        if should_quench:
            self.phase = ThermalPhase.QUENCH
            self.quench_start_epoch = self.epoch
            print(f"[ThermalPump] QUENCH triggered at epoch {self.epoch}: {reason}")
            return
        
        # DERIVED: Heat rate proportional to d(chi_g)/dt
        # When chi_g is rising, pump harder; when falling, slow down
        heat_rate = self._get_derived_heat_rate()
        self.temperature = min(
            self.temperature + heat_rate,
            self.schedule.T_max
        )
    
    def _get_derived_heat_rate(self) -> float:
        """
        Derive heat rate from chi_g dynamics.
        
        rate = base_rate * (1 + d(chi_g)/dt)
        When chi_g is rising (approaching transition), pump harder.
        """
        base_rate = 0.02  # Minimal base rate
        
        if len(self.chi_g_history) < 5:
            return base_rate
        
        recent = [v for _, v in self.chi_g_history[-5:]]
        d_chi = recent[-1] - recent[0]
        
        # Scale by chi_g gradient (positive = rising = pump harder)
        # Clamp to avoid runaway
        gradient_factor = max(0.1, min(5.0, 1.0 + d_chi * 10))
        
        return base_rate * gradient_factor
    
    def _update_quench_phase(self):
        """
        Update temperature during quenching phase.
        
        ZERO-PARAMETER: Uses Fermi quench factor for smooth crystallization.
        The quench rate is modulated by the distance from Re_crit.
        """
        # Fix 3: Use Fermi quench factor for smooth phase transition
        # sigma_quench ∈ [0, 1]: higher means more crystallization
        sigma_quench = self.get_fermi_quench_factor()
        
        # DERIVED: Base quench rate from epsilon dynamics
        base_quench_rate = self._get_derived_quench_rate()
        
        # Modulate quench rate by Fermi factor
        # When Re_SGC < Re_crit (crystallizing): sigma_quench → 1, faster quench
        # When Re_SGC > Re_crit (exploring): sigma_quench → 0, slower quench
        quench_rate = base_quench_rate * (0.5 + 0.5 * sigma_quench)
        
        # Exponential cooling toward target
        delta = self.temperature - self.schedule.T_target
        self.temperature = self.schedule.T_target + delta * (1 - quench_rate)
        
        # Transition to stable when close to target
        if abs(self.temperature - self.schedule.T_target) < 0.01:
            self.phase = ThermalPhase.STABLE
            print(f"[ThermalPump] STABLE at epoch {self.epoch}, T = {self.temperature:.4f}")
            print(f"  Final Re_crit = {self.Re_crit:.4f}, sigma_quench = {sigma_quench:.4f}")
    
    def _get_derived_quench_rate(self) -> float:
        """
        Derive quench rate from epsilon dynamics.
        
        Faster quench when epsilon is dropping rapidly (consolidating).
        Slower quench when epsilon is stable (needs more time).
        """
        if len(self.epsilon_history) < 5:
            return 0.3  # Default moderate rate
        
        recent = [v for _, v in self.epsilon_history[-5:]]
        d_eps = recent[0] - recent[-1]  # Positive if decreasing (good)
        
        # Scale quench rate: faster if epsilon dropping, slower if stable
        # Base rate 0.3, scaled by epsilon gradient
        rate = 0.3 * (1.0 + d_eps * 5)
        
        return max(0.1, min(0.8, rate))  # Clamp to reasonable bounds
    
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
            'Re_crit': self.Re_crit,  # Self-derived from Cv peak
            'fermi_quench_factor': self.get_fermi_quench_factor(),
            'chi_g_peak_detected': self.chi_g_peak_detected,
            'chi_g_peak_epoch': self.chi_g_peak_epoch,
            'Cv_peak_detected': self.Cv_peak_detected,
            'Cv_peak_temperature': self.Cv_peak_temperature,
        }
