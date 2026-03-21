# core.py
"""
SGCProfile dataclass — the complete emergence profile for a system (V, L, π).
Every field traces to a proved theorem or is labeled AXIOM/CONJECTURE/EMPIRICAL.
"""
import numpy as np
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any
from .certificates import CITATIONS, TheoremCitation, Prediction, get_citation


@dataclass
class SGCProfile:
    """
    The complete SGC emergence profile for a system (V, L, π).
    Every field is either a proved theorem or labeled AXIOM/CONJECTURE.
    """
    # Raw system
    L: np.ndarray                    # generator matrix (n×n)
    pi: np.ndarray                   # stationary distribution (n,)
    
    # The five SGC numbers
    epsilon: float = 0.0             # defect norm ‖D_{P*}‖_π  [theorem: optimal_partition_exists]
    gamma: float = 0.0               # spectral gap             [theorem: dirichlet_gap_non_decrease]
    T_star: float = 0.0              # validity horizon 1/ε     [theorem: trajectory_closure_bound]
    q: float = 1.0                   # Tsallis index            [theorem: tsallis_dpi]
    N_E: float = 0.0                 # emergence capacity       [axiom: emergence_ceiling]
    
    # Optimal partition
    P_star: np.ndarray = None        # partition assignment (n,) — integer labels
    n_blocks: int = 1                # number of blocks in P*
    defect_by_k: Dict[int, float] = field(default_factory=dict)  # {k: epsilon(k)} for k=1..n
    
    # Spectral data
    eigenvalues: np.ndarray = None   # eigenvalues of L (sorted by magnitude)
    timescales: np.ndarray = None    # -1/Re(λ_k) for λ_k ≠ 0
    n_timescale_gaps: int = 0        # autopoietic depth d(L,π)
    
    # Dirichlet decomposition
    dirichlet_coarse: float = 0.0    # ⟨f, L̄f⟩_π component
    dirichlet_leakage: float = 0.0   # ⟨f, Df⟩_π component
    
    # Schur complement (second-order correction)
    schur_correction_norm: float = 0.0  # ‖D·L_fine⁻¹·D‖_π — the self-energy magnitude
    
    # Predictions (populated after profile is built)
    predictions: List[Prediction] = field(default_factory=list)
    
    # Certificate
    citations: Dict[str, TheoremCitation] = field(default_factory=lambda: CITATIONS.copy())
    system_name: str = "unnamed"
    
    # Additional metadata
    labels: Optional[List[str]] = None  # state labels if provided
    q_diagnostics: Dict[str, Any] = field(default_factory=dict)
    
    def __post_init__(self):
        """Initialize arrays to proper defaults."""
        if self.P_star is None:
            self.P_star = np.zeros(len(self.pi), dtype=int)
        if self.eigenvalues is None:
            self.eigenvalues = np.array([])
        if self.timescales is None:
            self.timescales = np.array([])
    
    @property
    def n(self) -> int:
        """Number of states."""
        return len(self.pi)
    
    @property
    def autopoietic_depth(self) -> int:
        """
        Number of well-separated timescale clusters = levels of emergent description.
        Bounded by ⌊log₂(n)⌋. [theorem: rg_tower_terminates — proved from finiteness]
        """
        return self.n_timescale_gaps
    
    @property  
    def validity_horizon_label(self) -> str:
        """Human-readable label for validity horizon."""
        if self.T_star > 100:
            return "ROBUST (T* > 100)"
        elif self.T_star > 10:
            return "MODERATE (10 < T* ≤ 100)"
        elif self.T_star > 1:
            return "FRAGILE (1 < T* ≤ 10)"
        else:
            return "CRITICAL (T* ≤ 1)"
    
    @property
    def regime(self) -> str:
        """The three regimes from the emergence ceiling theorem."""
        if self.gamma < 0.01:
            return "CRITICAL (γ→0, N_E→∞, phase transition)"
        elif self.gamma > 10:
            return "THERMAL (γ>>1, no coarse structure)"
        else:
            return "EMERGENT (intermediate γ)"
    
    def add_prediction(self, statement: str, theorem_key: str, 
                       predicted_value: float, tolerance: float) -> Prediction:
        """Add a falsifiable prediction to be evaluated later."""
        pred = Prediction(
            statement=statement,
            theorem=get_citation(theorem_key),
            predicted_value=predicted_value,
            tolerance=tolerance
        )
        self.predictions.append(pred)
        return pred
    
    def evaluate_prediction(self, index: int, actual_value: float) -> Prediction:
        """Evaluate a prediction by index."""
        if 0 <= index < len(self.predictions):
            return self.predictions[index].evaluate(actual_value)
        raise IndexError(f"Prediction index {index} out of range")
    
    def summary_dict(self) -> Dict[str, Any]:
        """Return a dictionary summary of the profile."""
        return {
            "system_name": self.system_name,
            "n_states": self.n,
            "epsilon": self.epsilon,
            "gamma": self.gamma,
            "T_star": self.T_star,
            "q": self.q,
            "N_E": self.N_E,
            "n_blocks": self.n_blocks,
            "autopoietic_depth": self.autopoietic_depth,
            "regime": self.regime,
            "validity": self.validity_horizon_label,
            "schur_correction_norm": self.schur_correction_norm,
            "dirichlet_coarse": self.dirichlet_coarse,
            "dirichlet_leakage": self.dirichlet_leakage,
        }


class SGCDiagnostic:
    """
    The main engine for computing SGC emergence profiles.
    Agnostic to data source — takes (L, pi, labels) as input.
    """
    
    def __init__(self, L: np.ndarray, pi: np.ndarray, 
                 labels: Optional[List[str]] = None,
                 system_name: str = "unnamed"):
        """
        Initialize the diagnostic engine.
        
        Args:
            L: Generator matrix (n×n), rows sum to zero
            pi: Stationary distribution (n,), sums to 1
            labels: Optional state labels
            system_name: Name for this system
        """
        self.L = np.asarray(L, dtype=float)
        self.pi = np.asarray(pi, dtype=float)
        self.labels = labels
        self.system_name = system_name
        
        # Validate inputs
        n = len(self.pi)
        assert self.L.shape == (n, n), f"L must be {n}x{n}, got {self.L.shape}"
        assert np.allclose(self.pi.sum(), 1.0), f"π must sum to 1, got {self.pi.sum()}"
        assert np.all(self.pi > 0), "All π values must be positive"
        
        # Check generator property (rows sum to zero)
        row_sums = self.L.sum(axis=1)
        if not np.allclose(row_sums, 0, atol=1e-10):
            print(f"Warning: L row sums not zero (max deviation: {np.max(np.abs(row_sums))})")
    
    def compute_profile(self, k_min: int = 2, k_max: int = None, 
                        n_restarts: int = 20) -> SGCProfile:
        """
        Compute the complete SGC emergence profile.
        
        Args:
            k_min: Minimum number of partition blocks to try
            k_max: Maximum number of partition blocks (default: n//2)
            n_restarts: Number of random restarts for partition search
            
        Returns:
            SGCProfile with all measurements and citations
        """
        from .partition import find_optimal_partition, compute_projector, compute_defect_operator, defect_norm_pi
        from .spectral import (compute_spectral_gap, compute_timescales, 
                               count_timescale_gaps, decompose_dirichlet,
                               compute_schur_correction)
        from .tsallis import estimate_tsallis_q
        
        n = len(self.pi)
        
        # 1. Find optimal partition
        P_star, epsilon, defect_by_k = find_optimal_partition(
            self.L, self.pi, k_min=k_min, k_max=k_max, n_restarts=n_restarts
        )
        n_blocks = len(np.unique(P_star))
        
        # 2. Compute spectral properties
        gamma, eigenvalues = compute_spectral_gap(self.L, self.pi)
        timescales = compute_timescales(eigenvalues)
        n_timescale_gaps = count_timescale_gaps(timescales)
        
        # 3. Compute T* = validity horizon
        T_star = 1.0 / epsilon if epsilon > 1e-12 else float('inf')
        
        # 4. Estimate Tsallis q
        q, q_diagnostics = estimate_tsallis_q(self.pi)
        
        # 5. Compute emergence capacity N_E = b₁/(γ·ε)
        # b₁ ≈ n-1 for connected graphs (first Betti number of complete graph)
        b1 = n - 1  # approximation
        if gamma > 1e-12 and epsilon > 1e-12:
            N_E = b1 / (gamma * epsilon)
        else:
            N_E = float('inf')
        
        # 6. Compute Dirichlet decomposition on a test function
        Pi = compute_projector(self.pi, P_star)
        # Use the first non-constant eigenfunction as test function
        _, eigenvecs = np.linalg.eig(self.L)
        idx = np.argsort(np.abs(np.linalg.eigvals(self.L)))
        if len(idx) > 1:
            f_test = np.real(eigenvecs[:, idx[1]])  # slowest non-trivial mode
            f_test = f_test / np.sqrt(np.sum(self.pi * f_test**2))  # normalize in L²(π)
        else:
            f_test = np.ones(n) / np.sqrt(n)
        dirichlet_coarse, dirichlet_leakage = decompose_dirichlet(
            self.L, self.pi, Pi, f_test
        )
        
        # 7. Compute Schur correction
        Sigma = compute_schur_correction(self.L, self.pi, P_star)
        schur_correction_norm = defect_norm_pi(Sigma, self.pi)
        
        # Build profile
        profile = SGCProfile(
            L=self.L,
            pi=self.pi,
            epsilon=epsilon,
            gamma=gamma,
            T_star=T_star,
            q=q,
            N_E=N_E,
            P_star=P_star,
            n_blocks=n_blocks,
            defect_by_k=defect_by_k,
            eigenvalues=eigenvalues,
            timescales=timescales,
            n_timescale_gaps=n_timescale_gaps,
            dirichlet_coarse=dirichlet_coarse,
            dirichlet_leakage=dirichlet_leakage,
            schur_correction_norm=schur_correction_norm,
            system_name=self.system_name,
            labels=self.labels,
            q_diagnostics=q_diagnostics,
        )
        
        return profile
